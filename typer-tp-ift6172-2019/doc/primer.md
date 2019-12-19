# Typer Primer

## Basic functional programming

Typer at its core is a fairly standard statically typed functional
programming language, and shares a lot with languages like Haskell, OCaml,
SML, ...

### Simple definitions

A file is composed of a sequence of declarations, which are mostly made of
definitions.  For example, you can define a new variable with `<var> = <exp>`:

    x = 4;

Note that the `;` does not *terminate* declarations but *separates* them so
it's not needed at the very end of a sequence of declarations.

You can also declare the type of a variable type before giving its definition:

    y : Int;
    y = 5;

### Function definitions

You can define functions with the syntax `f <args> = <exp>`:

    sub x y = x - y;

A function call like `sub 47 5` will then return `42`.

You can also use anonymous functions with the expression
`lambda <args> -> <exp>`, so the above definition is syntactic sugar for:

    sub = lambda x y -> x - y;

There is hence a single namespace for functions and other variables.
Functions are curried, so you can use `sub 0` as a function of one
argument which returns its negative.

The type of `sub` above could be written as:

    sub : Int -> Int -> Int;

but you can also give names to the arguments in the type signature:

    sub : (x : Int) -> (y : Int) -> Int

### Type definitions

You can define a new algebraic datatype with
`type <name> | <cons1> <args1> | ...`.  For example the types of pairs and
booleans can be defined as:

    type Bool
       | true
       | false;
    type Pair a b
       | pair a b;

after which you can construct a pair for example with `pair 5 6`:
constructors are invoked like functions, and are curried.  To extract
information from an algebraic datatype, you have to use `case` whose syntax
is `case <exp> | <cons1> <args1> => <exp1> | ...`.  For example:

    not b = case b
            | true => false
            | false => true;
    left x = case x | pair l _ => l;
    right x = case x | pair _ r => r;

Types share also the same namespace as other variables.

You can name your fields in type constructors:

    type Pair a b | pair (left : a) (right : b);

This can be used to pass arguments by name rather than by position.
For example, you can then construct a pair with either of:

    x = pair 5 6;
    y = pair (right := 6) (left := 5);
    left x = case x | pair (left := l) _ => l;
    right x = case x | pair (right := r) _ => r;

You can also use such named arguments for normal functions.
E.g. `sub (y := 5) 47` would also return 42.

### Recursion

Type annotations play a double role: they also play the role of forward
declarations.  They are needed in recursive declarations.  For example, when
defining the (recursive) type of simply-linked lists, you'd need:

    List : Type -> Type;
    type List a
       | nil
       | cons a (List a)

This is also needed for mutual recursion:

    odd : Int -> Int;
    even : Int -> Int;
    odd x  = case Int_eq x 0
             | true => false
             | false => even (x - 1);
    even x = case Int_eq x 0
             | true => true
             | false => odd (x - 1);

### Polymorphism

In the above `Pair` example, the type is polymorphic in that each field can
have any type.  The real type of the `pair` constructor is:

    pair : (a : Type) ≡> (b : Type) ≡> a -> b -> Pair a b

Where `(x : t) ≡> e` is used to specify arguments that are implicit and only
exist for type-checking purposes, so you can just call `pair 5 6` and let
Typer infer the types `a` and `b`.  This said, if you want, you can provide
those type arguments explicitly using the named arguments syntax:

    p = pair (a := Int) (b := Int -> Int) 5 (lambda x -> x);

## Macros

Typer macros are modeled after Lisp macros, so they mostly manipulate the
program represented as an S-expression.

### S-expressions

S-expressions are represented using the `Sexp` type.  This type is internal,
but is conceptually equivalent to the following datatype:

    type Sexp
       | symbol String
       | string String
       | integer Int
       | float Float
       | node Sexp (List Sexp)

Because it is not defined as an datatype, you currently cannot match it with
`case` and construct elements in the usual way.  Instead, you need to use
the following constructors:

    Sexp_symbol  : String    -> Sexp;
    Sexp_string  : String    -> Sexp;
    Sexp_integer : Int       -> Sexp;
    Sexp_float   : Float     -> Sexp;
    Sexp_node    : Sexp -> List Sexp -> Sexp;

and the following dispatch function:

    Sexp_dispatch : (a : Type) ≡>
                    Sexp
                    -> (node   : Sexp -> List Sexp -> a)
                    -> (symbol : String -> a)
                    -> (string : String -> a)
                    -> (int    : Int -> a)
                    -> (float  : Float -> a)
                    -> (block  : List Sexp -> a)
                    -> a;

### Parsing code as S-expressions

Contrary to Lisp, Typer uses an infix (or rather mixfix) syntax, so its
notion of S-expressions is a bit more complex than that of Lisp.  When Typer
code is parsed its first turned into an S-expression where mixfix syntax is
replaced with "standard" prefix syntax.  The source code does not actually
need to use the mixfix syntax and can always use the prefix syntax instead.

The conversion between the two basically adds the `_` character to the
combination of keywords that make up a given mixfix construction.
For example, the term `a + b` gets converted to `_+_ a b` and the `lambda
x -> e` term turns into `lambda_->_ x e`.

Here's a more complex example:

    type List a
       | nil
       | cons (hd : a) (tl : List a)

turns into

    type_ (_|_ (List a)
               nil
               (cons (_:_ hd a) (_:_ tl (List a))))

Those above two forms are completely indistinguishable to Typer.
Note that contrary to Lisp, parentheses are not significant (other than to
clarify structure), so you can add parentheses anywhere you want as long as
they don't affect the structure.

### Macro definitions

A macro is little more than a function of S-expressions, which is invoked at
compile time.  To turn such a function into a macro, just wrap it in the
`macro` constructor:

    fun = macro (lambda args -> Sexp_node (Sexp_symbol "lambda_->_") args);
    
after which you can use it with the normal "function call" syntax:

    inc1 = fun x (x + 1);

which will macroexpand to:

    inc1 = lambda_->_ x (x + 1);
