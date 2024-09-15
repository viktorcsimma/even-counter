For the parser, I chose
[the one from the Functional Languages course](https://github.com/akaposi/ELTE-func-lang/blob/master/2022-23-2/gyak1/Gy10.hs)
as a starting point.
However, I rewrote it in Agda;
as the types can easily be defined in it
and proofs can guarantee the operations are indeed legal.

I have similar Exp and Statement types,
except that they get the underlying approximate rational type
as a type parameter:

```hs
-- TODO: paste the Agda version
data Exp a = BoolLiteral Bool           -- "true", "false"
           | IntLiteral Integer         -- "-?[1-9][0-9]*"
           | RationalLiteral Rational   -- "/", if both sides are integers
           | RealLiteral (C a)          -- "pi" would be RealLiteral pi, for example
           -- unary operators
           | Neg (Exp a)                -- "-"
           | Recip (Exp a)              -- "recip"
           | Sqrt (Exp a)               -- "sqrt"
           | Sin (Exp a)                -- "sin"
           | Cos (Exp a)                -- "cos"
           | Arctg (Exp a)              -- "arctg"
           | Exponential (Exp a)        -- "exp"
           -- binary operators
           | Pow (Exp a) (Exp a)        -- "^"
           | Mul (Exp a) (Exp a)        -- "*"
           | Div (Exp a) (Exp a)        -- "/", if at least one of the operands is not an integer
           | Add (Exp a) (Exp a)        -- "+"
           | Sub (Exp a) (Exp a)        -- "-"
           | And (Exp a) (Exp a)        -- "&&"
           | Or (Exp a) (Exp a)         -- "||"
           | Equal (Exp a) (Exp a)      -- "=="
           | Less (Exp a) (Exp a)       -- "<"
           | LessEq (Exp a) (Exp a)     -- "<="
           | Greater (Exp a) (Exp a)    -- ">"
           | GreaterEq (Exp a) (Exp a)   -- ">="
           -- variables
           | Var String                 -- string which is not a keyword and starts with a letter
           | HistoryItem Int            -- history[n] where n is an index; history[0] is equivalent to Ans)

data Statement a
           = Assign String (Exp a)      -- "=" (or implicitly "Ans = ...", when only an expression is given)
           | If (Exp a) [Statement]     -- if (cond) {p₁}
           | While (Exp a) [Statement]  -- while (cond) {p₁}
```

A variable has one of 4 possible types;
evaluating an expression has a result of Value a:

```
data Value a
           = BoolValue Bool
           | IntValue Integer
           | RationalValue Rational
           | RealValue (C a)
```

The normalisation is relatively straightforward,
using the variables stored in the CalcState instance
and functions from Acorn.
For real comparisons,
I check whether I can decide based on
approximations of a pre-defined precision.
If yes, I return a Bool;
if not, I throw an error.
Reciprocals and divisions imply
a comparison with 0.

Other changes include:
- rewriting the parser in Agda;
- switching to a C-style syntax;
- using Either instead of Maybe;
- adding unary operators (negate is now hard-wired);
- adding subtraction and division.
