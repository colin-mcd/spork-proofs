--import SporkProofs.IVec
import SporkProofs.Syntax
-- open Lean Elab Command Term Macro

@[simp] abbrev mkfunc : List Block -> Func
  | bs => Func.mk (FuncSig.mk (getarity bs) (getret bs)) bs
  where
    getarity : List Block -> Nat
      | [] => panic "cannot infer signature of empty function!"
      | .mk bsig _ :: _ => bsig.arity
    coderet : Code -> Option Nat
      | .stmt _e c => coderet c
      | .retn rs => some rs.length
      | _ => none
    getret : List Block -> Nat
      | [] => panic "cannot infer signature of function because it has no return!"
      | .mk _ code :: bs => (coderet code).getD (getret bs)

declare_syntax_cat ssa_atom
declare_syntax_cat ssa_unaop
declare_syntax_cat ssa_binop
declare_syntax_cat ssa_expr
declare_syntax_cat stmtget
declare_syntax_cat BB
declare_syntax_cat opt_spork_sig

--syntax "var" "⟨" term "⟩" : term
syntax "list?" "[" term,* "]" : term
syntax (name := goto) "goto " term:max "(" term,* ")" : term
syntax (name := GOTO) "GOTO " term:max "(" term,* ")" : term
syntax (name := CALL) "CALL " term:max "(" term,* ")" "⊳" term : term
syntax (name := RETURN) "RETURN " "(" term,* ")" : term
syntax (name := SPORK) "SPORK " "(" term "," term:max "(" term,* ")" ")" : term
syntax (name := SPOIN) "SPOIN " "(" term "," term ")" : term
syntax (name := ITE) "IF " ssa_atom " THEN " term " ELSE " term : term
syntax num : ssa_atom
syntax ident : ssa_atom
syntax "¬" : ssa_unaop
syntax "-" : ssa_unaop
syntax "+" : ssa_binop
syntax "-" : ssa_binop
syntax "*" : ssa_binop
syntax "/" : ssa_binop
syntax "%" : ssa_binop
syntax "<" : ssa_binop
syntax "≤" : ssa_binop
syntax "<=" : ssa_binop
syntax ">" : ssa_binop
syntax "≥" : ssa_binop
syntax ">=" : ssa_binop
syntax "==" : ssa_binop
syntax "!=" : ssa_binop
syntax "&&" : ssa_binop
syntax "||" : ssa_binop
syntax "^^" : ssa_binop
syntax ssa_atom : ssa_expr
syntax ssa_unaop ssa_atom : ssa_expr
syntax ssa_atom ssa_binop ssa_atom : ssa_expr
syntax "[expr| " ssa_expr "]" : term
syntax "stmts " num "{" stmtget "}" : term
syntax term : stmtget
syntax ident " ← " ssa_expr "," stmtget : stmtget
syntax (name := countIdents) "countIdents " ident* : term
syntax (name := blocklets) "blocklets " ident* " from " num " in " term : term
syntax (name := somesporksig) ("sporks " "(" term,* ")")? : opt_spork_sig
syntax "block " ident "(" ident,* ")" ("sporks " "(" term,* ")")? "{" stmtget "}" : BB
syntax "func" "(" BB,* ")" : term
syntax "blocksh" "⟨" BB* "⟩" "⟨" ident* "⟩" "⟨" term:max* "⟩" "⟨" term:max* "⟩" : term
syntax "parseblocks" BB* : term

def bbToIdent : Lean.TSyntax `BB → Lean.TSyntax `ident
  | `(BB| block $x:ident ($_args,*) {$_cs}) => x
  | `(BB| block $x:ident ($_args,*) sporks ($_ss) {$_cs}) => x
  | _ => panic "unknown syntax for basic block"

def elabSSAAtom : Lean.Macro
  | `(ssa_atom| $n:num) => `(Atom.val ($n))
  | `(ssa_atom| $x:ident) => `(Atom.var (Var.mk ($x)))
  | _ => Lean.Macro.throwUnsupported

def elabSSAUop : Lean.Macro
  | `(ssa_unaop| -) => `(Uop.INEG)
  | `(ssa_unaop| ¬) => `(Uop.LNOT)
  | _ => Lean.Macro.throwUnsupported

def elabSSABop : Lean.Macro
  | `(ssa_binop| +)  => `(Bop.IADD)
  | `(ssa_binop| -)  => `(Bop.ISUB)
  | `(ssa_binop| *)  => `(Bop.IMUL)
  | `(ssa_binop| /)  => `(Bop.IDIV)
  | `(ssa_binop| %)  => `(Bop.IMOD)
  | `(ssa_binop| <)  => `(Bop.ILT)
  | `(ssa_binop| <=) => `(Bop.ILE)
  | `(ssa_binop| ≤)  => `(Bop.ILE)
  | `(ssa_binop| >)  => `(Bop.IGT)
  | `(ssa_binop| >=) => `(Bop.IGE)
  | `(ssa_binop| ≥)  => `(Bop.IGE)
  | `(ssa_binop| ==) => `(Bop.IEQ)
  | `(ssa_binop| !=) => `(Bop.INE)
  | `(ssa_binop| &&) => `(Bop.LAND)
  | `(ssa_binop| ||) => `(Bop.LOR)
  | `(ssa_binop| ^^) => `(Bop.LXOR)
  | _ => Lean.Macro.throwUnsupported

macro_rules
  -- if only one element, first try to use that element
  -- as the list itself, otherwise a singleton
  -- this parses both list?[1,2,3] and list?[x] for some list x
  | `(list?[$x:term]) => `(by first | exact [($x)] | exact ($x))
  | `(list?[$xs,*]) => `([$xs,*])

  | `(goto $b ($args,*)) => `(Cont.mk ($b) list?[$args,*])

  | `(CALL $f ($args,*) ⊳ $cont) => `(Code.call ($f) list?[$args,*] ($cont))
  | `(RETURN ($args,*)) => `(Code.retn list?[$args,*])
  | `(GOTO $b ($args,*)) => `(Code.goto (goto $b ($args,*)))
  | `(SPORK ($body, $f ($args,*) ) ) => `(Code.spork ($body) ($f) list?[$args,*])
  | `(SPOIN ($unpr, $prom)) => `(Code.spoin ($unpr) ($prom))
  | `(IF $cond THEN $tt ELSE $ff) =>
      elabSSAAtom cond >>= λ cond' =>
      `(Code.ite ($(⟨cond'⟩)) ($tt) ($ff))

  | `(ssa_expr| $a:ssa_atom) =>
      elabSSAAtom a >>= λ a' =>
      `(Expr.nop ($(⟨a'⟩)))
  | `(ssa_expr| $o:ssa_unaop $a:ssa_atom) =>
      elabSSAUop o >>= λ o' =>
      elabSSAAtom a >>= λ a' =>
      `(Expr.uop ($(⟨o'⟩)) ($(⟨a'⟩)))
  | `(ssa_expr| $a:ssa_atom $o:ssa_binop $b:ssa_atom) =>
      elabSSABop o >>= λ o' =>
      elabSSAAtom a >>= λ a' =>
      elabSSAAtom b >>= λ b' =>
      `(Expr.bop ($(⟨o'⟩)) ($(⟨a'⟩)) ($(⟨b'⟩)))

  | `([expr| $se:ssa_expr ]) => `($(⟨se.1⟩))

  | `(stmts $_ { $t:term }) => `($t)
  | `(stmts $i { $x:ident ← $t:ssa_expr, $s:stmtget }) =>
      `(Code.stmt ([expr|$t]) (let $x := Var.mk ($i); stmts $(Lean.Syntax.mkNatLit i.getNat.succ) { $s }))

  | `(countIdents $ids:ident*) =>
      let n := ids.size
      return Lean.Syntax.mkNatLit n

  | `(blocklets from $_ in $t) => `($t)
  | `(blocklets $x:ident $xs:ident* from $i in $t) =>
      `(let $x := $i; blocklets $xs* from $(Lean.Syntax.mkNatLit i.getNat.succ) in $t)

  | `(func ($bbs,*)) => `(mkfunc (blocklets $(bbs.getElems.map bbToIdent)* from 0 in parseblocks $bbs*))
  | `(parseblocks) => `([])
  | `(parseblocks block $x:ident ($args:ident,*) {$cs:stmtget} $bbs:BB*) =>
      `(Block.mk (BlockSig.mk $(Lean.Syntax.mkNatLit args.getElems.size) []) (blocklets $args* from 0 in stmts 0 {$cs}) :: parseblocks $bbs*)
  | `(parseblocks block $x:ident ($args:ident,*) sporks ($ss:term,*) {$cs:stmtget} $bbs:BB*) =>
      `(Block.mk (BlockSig.mk $(Lean.Syntax.mkNatLit args.getElems.size) list?[$ss,*]) (blocklets $args* from 0 in stmts 0 {$cs}) :: parseblocks $bbs*)
