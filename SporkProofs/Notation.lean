import SporkProofs.Syntax
import SporkProofs.WFSyntax
open Lean Elab Macro

/-!
DSL notation for Spork IR, allowing nice syntax for constructing programs.
After parsing a program, it runs a very basic "type inference" which infers
the signatures of functions and basic blocks.

Example (for `f g : FuncIdx`):
```
func (
  block start():
    SPORK (goto body(), goto spwn())
  block body():
    CALL f() ⊳ goto cont()
  block cont(a):
    SPOIN (goto unpr(a), goto prom(a))
  block unpr(a):
    CALL g() ⊳ goto ret(a)
  block prom(r₁, r₂):
    GOTO ret(r₁,r₂)
  block ret(a, b):
    RETURN(a,b)
  block spwn():
    CALL g() ⊳ goto exit()
  block exit(b):
    RETURN(b)
)
```
-/

/--
Raw, unannotated block (signature to be inferred later).
Stores the name string for better error messages.
-/
inductive UnannotatedBlock where
  | mk (name: String) (args : Scope) (c : Code)
  deriving Inhabited

/--
Runs "type inference" on a list of unannotated blocks,
returning a Func with a FuncSig and Blocks with their BlockSigs
-/
@[simp] abbrev mkfunc (fname : String) : List UnannotatedBlock -> Func
  | bs => let bs' := infer_bsigs bs
          Func.mk (getfsig bs') bs'
  where
    
    @[simp] rsig_retn := true
    @[simp] rsig_exit := false

    @[simp] infer_rsigs_h (bs : List UnannotatedBlock) (rsigs : List (Option Bool)) : List (Option Bool) :=
      Nat.fold bs.length
        (λ i ilt rsigs =>
          if let some rsig := rsigs[i]? then
          match bs[i].3.split.2 with
           | ⟨.stmt e c, notstmt⟩ => nomatch notstmt e c
           | ⟨.goto bnext, _⟩ => rsigs.set bnext.b rsig
           | ⟨.ite cond bthen belse, _⟩ => (rsigs.set bthen.b rsig).set belse.b rsig
           | ⟨.call f args bret, _⟩ => rsigs.set bret.b rsig
           | ⟨.retn args, _⟩ => rsigs
           | ⟨.spork bbody bspwn, _⟩ => (rsigs.set bbody.b rsig).set bspwn.b rsig_exit
           | ⟨.spoin bunpr bprom, _⟩ => (rsigs.set bunpr.b rsig).set bprom.b rsig
          else rsigs)
        rsigs
    
    /--
    Determines whether each block is part of a returning component or an exiting one.
    Initially, we only know that the entry block must be a return.
     -/
    @[simp] infer_rsigs (bs : List UnannotatedBlock) : List (Option Bool) :=
      Nat.repeat (infer_rsigs_h bs) bs.length
        (some rsig_retn :: List.replicate bs.length.pred none)
    
    @[simp] getfsig : List Block -> FuncSig
      | [] => panic "cannot infer signature of empty function!"
      | .mk ⟨Γ, r, _σ⟩ _c :: _rest => .mk Γ r.n

    @[simp] get_bsig' (bs : List (UnannotatedBlock ⊕ Block)) (b : Cont) : Option BlockSig :=
      bs[b.b]? >>= Sum.elim (λ _ => none) (λ b => some b.bsig)

    @[simp] get_bsig (bs : List (UnannotatedBlock ⊕ Block)) (b : Cont) : Option (ResultSig × List Nat) :=
      (get_bsig' bs b).map (λ bsig => (bsig.r, bsig.σ))

    @[simp] mkrsig (rsig : Bool) : Nat -> ResultSig :=
      if rsig = rsig_retn then
        ResultSig.retn
      else
        ResultSig.exit

    @[simp] infer_bsig (rsig : Bool) (bs : List (UnannotatedBlock ⊕ Block)) : Code -> Option (ResultSig × List Nat)
      | .stmt _e c => infer_bsig rsig bs c
      | .goto bnext => get_bsig bs bnext
      | .ite _cond bthen belse => get_bsig bs bthen <|> get_bsig bs belse
      | .call _f _args bret => get_bsig bs bret
      | .retn args => some (mkrsig rsig args.length, [])
      | .spork bbody _bspwn =>
        (get_bsig bs bbody).map (λ (r, σ) => (r, σ.tail))
      | .spoin _bunpr bprom =>
        (get_bsig' bs bprom).map (λ bsig => (bsig.r, (bsig.Γ - bprom.args.length) :: bsig.σ))

    @[simp] infer_bsigs_h (rsigs : List Bool)
                          (bs : List (UnannotatedBlock ⊕ Block)) :
                          List (UnannotatedBlock ⊕ Block) :=
      bs.mapIdx λ i b =>
        b.elim (λ ub => (infer_bsig rsigs[i]! bs ub.3).elim b
                          λ (r, σ) => .inr ⟨⟨ub.2, r, σ⟩, ub.3⟩)
               .inr
    @[simp] infer_bsigs (ubs: List UnannotatedBlock) : List Block :=
      let rsigs := infer_rsigs ubs
      let rsigs := rsigs.mapIdx (λ i r => r.elim (panic ("failed to infer result signature for block " ++ ubs[i]!.1 ++ " in function " ++ fname)) (·))
      let xs := Nat.repeat (infer_bsigs_h rsigs) ubs.length (ubs.map Sum.inl)
      xs.map (·.elim (λ ub => panic ("failed to infer signature for block " ++ ub.1 ++ " in function " ++ fname)) (·))

declare_syntax_cat ssa_atom
declare_syntax_cat ssa_unaop
declare_syntax_cat ssa_binop
declare_syntax_cat ssa_expr
declare_syntax_cat stmtget
declare_syntax_cat BB
declare_syntax_cat PF

--syntax "var" "⟨" term "⟩" : term
syntax "list?" "[" term,* "]" : term
syntax (name := goto) "goto " term:max "(" term,* ")" : term
syntax (name := GOTO) "GOTO " term:max "(" term,* ")" : term
syntax (name := CALL) "CALL " term:max "(" term,* ")" "⊳" term : term
syntax (name := RETURN) "RETURN " "(" term,* ")" : term
syntax (name := SPORK) "SPORK " "(" term "," term ")" : term
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
syntax (name := blockletssyntax) "blocklets " ident* " from " num " in " term : term
syntax "block " ident "(" ident,* ")" ": " stmtget : BB
syntax "block " "(" ident,* ")" ": " stmtget : term
syntax "func " ident "(" BB* ")" : PF
syntax "func " "(" BB* ")" : term
syntax "parseblocks" BB* : term
syntax "parsefuncs" PF*: term
syntax "PROGRAM" "(" PF,* ")" : term

def bbToIdent : Lean.TSyntax `BB → Lean.TSyntax `ident
  | `(BB| block $x:ident ($_args,*): $_cs) => x
--  | `(BB| block $x:ident ($_args,*) sporks ($_ss) {$_cs}) => x
  | _ => panic "unknown syntax for basic block"

def identToStr : Lean.TSyntax `ident → Lean.TSyntax `term
  | `($x:ident) => Lean.Syntax.mkStrLit ((Lean.TSyntax.getId x).toString)
  | _ => panic "expected identifier in identToStr"

def bbToStr : Lean.TSyntax `BB → Lean.TSyntax `term
  | `(BB| block $x:ident ($_args,*): $_cs) => identToStr x -- Lean.Syntax.mkStrLit ((Lean.TSyntax.getId x).toString)
  | _ => panic "unknown syntax for basic block"

def pfToIdent : Lean.TSyntax `PF → Lean.TSyntax `ident
  | `(PF| func $x:ident ($_bb*)) => x
  | _ => panic "unknown syntax for function"

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
  | `(SPORK ($body, $spwn)) => `(Code.spork ($body) ($spwn))
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
      `(let $x := $i
        blocklets $xs* from $(Lean.Syntax.mkNatLit i.getNat.succ) in $t)

  | `(func ($bbs*)) => `(mkfunc "_" (blocklets $(bbs.map bbToIdent)* from 0 in parseblocks $bbs*))
  | `(parsefuncs) => `([])
  | `(parsefuncs func $x:ident ($bbs*) $pfs:PF*) =>
    `(mkfunc $(identToStr x) (blocklets $(bbs.map bbToIdent)* from 0 in parseblocks $bbs*) :: parsefuncs $pfs*)
  | `(PROGRAM ($pfs,*)) =>
    `(Program.mk (blocklets $(pfs.getElems.map pfToIdent)* from 0 in parsefuncs $pfs*))

  | `(parseblocks) => `([])
  | `(parseblocks block $x:ident ($args:ident,*): $cs:stmtget $bbs:BB*) =>
      `(UnannotatedBlock.mk $(identToStr x) $(Lean.Syntax.mkNatLit args.getElems.size) (blocklets $args* from 0 in stmts 0 {$cs}) :: parseblocks $bbs*)
  | `(block ($args:ident,*) : $cs:stmtget) =>
      `(UnannotatedBlock.mk "_" $(Lean.Syntax.mkNatLit args.getElems.size) (blocklets $args* from 0 in stmts 0 {$cs}))
