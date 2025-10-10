import SporkProofs.Syntax
import SporkProofs.Notation

def parSSA (f g : FuncIdx): Func :=
  func (
    block start() {SPORK (goto body(), g())},
    block body() sporks (1) {CALL f() ⊳ goto cont()},
    block cont(x) sporks (1) {SPOIN (goto unpr(x), goto prom(x))},
    block unpr(x) {CALL g() ⊳ goto ret(x)},
    block prom(x, y) {GOTO ret(x,y)},
    block ret(x, y) {RETURN(x, y)}
  )

def redSSA (c f red split : FuncIdx) : Func × Func :=
  (func (
     block start(z,a,i,j) {GOTO guard(z,i,j,a)},
     block guard(z,i,j,a) {b ← i >= j, IF b THEN goto done(a) ELSE goto iter(z,i,j,a)},
     block done(a) {RETURN(a)},
     block iter(z,i,j,a) {SPORK (goto body(z,i,j,a), split(z,i,j,a))},
     block body(z,i,j,a) sporks (1) {CALL f(i) ⊳ goto accum(z,i,j,a)},
     block accum(z,i,j,a,a₁) sporks (1) {CALL c(a,a₁) ⊳ goto cont(z,i,j)},
     block cont(z,i,j,a) sporks (1) {SPOIN (goto next(z,i,j,a), goto brk(a))},
     block next(z,i,j,a) {i₁ ← i + 1, GOTO guard(z,i₁,j,a)},
     block brk(a,a₁) {CALL c(a,a₁) ⊳ goto done()}
   ),
   func (
     block spwn(z,a,i,j) {i₁ ← i + 1, k ← i₁ + j, m ← k / 2, SPORK (goto left(z,i₁,m,j), red(z,z,m,j))},
     block left(z,i,m,j) sporks (1) {CALL red(z,z,i,m) ⊳ goto middle(z,m,j)},
     block middle(z,m,j,a) sporks (1) {SPOIN(goto leftover(z,m,j,a), goto merge(a))},
     block leftover(z,m,j,a) {CALL red(z,a,m,j) ⊳ goto exit()},
     block merge(a,a₁) {CALL c(a,a₁) ⊳ goto exit()},
     block exit(a) {RETURN(a)}
   ))  

theorem parSSAWF : (parSSA 0 1).WF [FuncSig.mk 0 1, FuncSig.mk 0 1] :=
  by trivial
theorem redSSAWF :
    let fsigs := [FuncSig.mk 2 1, FuncSig.mk 1 1, FuncSig.mk 4 1, FuncSig.mk 4 1]
    (redSSA 0 1 2 3).fst.WF fsigs ∧ (redSSA 0 1 2 3).snd.WF fsigs :=
  by trivial
