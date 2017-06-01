{
{-# LANGUAGE GeneralizedNewtypeDeriving #-}
{-# LANGUAGE PartialTypeSignatures #-}

module Language.Equivalence.Parser (
    parseProg
  , parseTokens
  ) where

import Language.Equivalence.Lexer
import Language.Equivalence.Types
import Control.Monad.Except
import Control.Exception

}

-- Entry point
%name prog

-- Lexer structure
%tokentype { Token }

-- Parser monad
%monad { Except String } { (>>=) } { return }
%error { parseError }

-- Token Names
%token
    let   { LET _    }
    true  { TRUE _   }
    false { FALSE _  }
    in    { IN _     }
    if    { IF _     }
    then  { THEN _   }
    else  { ELSE _   }
    TNUM  { NUM _ $$ }
    ID    { ID _ $$  }
    '\\'  { LAM _    }
    '->'  { ARROW _  }
    '='   { EQB _    }
    '+'   { PLUS _   }
    '-'   { MINUS _  }
    '*'   { MUL _    }
    '&&'  { AND _    }
    '||'  { OR  _    }
    '=='  { EQL _    }
    '/='  { NEQ _    }
    '<'   { LESS _   }
    '<='  { LEQ _    }
    ':'   { COLON _  }
    '('   { LPAREN _ }
    ')'   { RPAREN _ }
    '['   { LBRAC _  }
    ']'   { RBRAC _  }
    ','   { COMMA _  }
    ';'   { SEMI _  }


-- Operators
%right in
%nonassoc '=' '==' '/=' '<' '<=' if then else
%right ':' '->'
%left '||' '&&'
%left '+' '-'
%left '*'
%%

Prog : Bind                         { [$1]    }
     | Bind ';'   Prog              { $1 : $3 }

Bind : Id Ids '=' Expr              { ($1, mkLam $2 $4) }

Expr : Expr ':' Expr                { EBin Cons  $1 $3 }
     | Expr '&&' Expr               { EBin And   $1 $3 }
     | Expr '||' Expr               { EBin Or    $1 $3 }
     | Expr '==' Expr               { EBin Eq    $1 $3 }
     | Expr '/=' Expr               { EBin Ne    $1 $3 }
     | Expr '<'  Expr               { EBin Lt    $1 $3 }
     | Expr '<=' Expr               { EBin Le    $1 $3 }
     | Expr '+'  Expr               { EBin Plus  $1 $3 }
     | Expr '-'  Expr               { EBin Minus $1 $3 }
     | Expr '*'  Expr               { EBin Mul   $1 $3 }
     | if Expr then Expr else Expr  { EIf  $2 $4 $6    }
     | '\\' Id '->' Expr            { ELam $2 $4       }
     | let Id '='  Expr in Expr     { ELet $2 $4 $6    }
     | let Id Ids '=' Expr in Expr  { ELet $2 (mkLam $3 $5) $7 }
     | Axpr                         { $1               }

Axpr : Axpr Bxpr                   { EApp $1 $2       }
     | Bxpr                        { $1               }


Bxpr : TNUM                        { EInt $1        }
     | true                        { EBool True     }
     | false                       { EBool False    }
     | '(' Expr ')'                { $2             }
     | Id                          { EVar $1        }
     | '[' ']'                     { ENil           }
     | '[' Exprs ']'               { exprList $2    }

Exprs : Expr                       { [$1]           }
      | Expr ',' Exprs             { $1 : $3        }

Ids : Id                           { [$1]       }
    | Id Ids                       { ($1) : $2  }

Id  : ID                           { Var $1         }

{
mkLam :: [Var] -> CoreExpr -> CoreExpr
mkLam []     e = e
mkLam (x:xs) e = ELam x (mkLam xs e)

parseError :: [Token] -> Except String a
parseError (l:ls) = throwError (show l)
parseError []     = throwError "Unexpected end of Input"

parseProg :: String -> Program
parseProg s = case parseProg' s of
                   Left msg -> throw (Error ("parse error:" ++ msg))
                   Right e  -> e

parseProg' input = runExcept $ do
   tokenStream <- scanTokens input
   prog tokenStream

parseTokens :: String -> Either String [Token]
parseTokens = runExcept . scanTokens


}
