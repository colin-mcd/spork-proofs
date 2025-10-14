import SporkProofs.Syntax
import SporkProofs.Notation
import SporkProofs.WFSyntax

def parSSAexample: Program :=
  let f := 0
  let g := 1
  .mk [
    func ()
    func (
      block start() {SPORK (goto body(), goto spwn())},
      block body() {CALL f() ⊳ goto cont()},
      block cont(x) {SPOIN (goto unpr(x), goto prom(x))},
      block unpr(x) {CALL g() ⊳ goto ret(x)},
      block prom(x, y) {GOTO ret(x,y)},
      block ret(x, y) {RETURN(x, y)},
      block spwn() {CALL g() ⊳ goto exit()},
      block exit(y) {RETURN(y)}
    )]


def redSSA (c f red : FuncIdx) : Func :=
  func (
    block start(z,a,i,j) {GOTO guard(z,i,j,a)},
    block guard(z,i,j,a) {b ← i >= j, IF b THEN goto done(a) ELSE goto iter(z,i,j,a)},
    block done(a) {RETURN(a)},
    block iter(z,i,j,a) {SPORK (goto body(z,i,j,a), goto split(z,i,j,a))},
    block body(z,i,j,a) {CALL f(i) ⊳ goto accum(z,i,j,a)},
    block accum(z,i,j,a,a₁) {CALL c(a,a₁) ⊳ goto cont(z,i,j)},
    block cont(z,i,j,a) {SPOIN (goto next(z,i,j,a), goto brk(a))},
    block next(z,i,j,a) {i₁ ← i + 1, GOTO guard(z,i₁,j,a)},
    block brk(a,a₁) {CALL c(a,a₁) ⊳ goto done()},
    block split(z,i,j,a) {i₁ ← i + 1, k ← i₁ + j, m ← k / 2, SPORK (goto left(z,i₁,m,j), goto right(z,m,j))},
    block left(z,i,m,j) {CALL red(z,z,i,m) ⊳ goto middle(z,m,j)},
    block middle(z,m,j,a) {SPOIN(goto leftover(z,m,j,a), goto merge(a))},
    block leftover(z,m,j,a) {CALL red(z,a,m,j) ⊳ goto exit()},
    block merge(a,a₁) {CALL c(a,a₁) ⊳ goto exit()},
    block exit(a) {RETURN(a)},
    block right(z,m,j) {CALL red(z,z,m,j) ⊳ goto exit()}
   )

theorem parSSAWF : (parSSA 0 1).WF [FuncSig.mk 0 1, FuncSig.mk 0 1] :=
  by trivial
theorem redSSAWF :
    let fsigs := [FuncSig.mk 2 1, FuncSig.mk 1 1, FuncSig.mk 4 1, FuncSig.mk 4 1]
    (redSSA 0 1 2).WF fsigs
  by trivial
