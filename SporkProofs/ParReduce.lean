import SporkProofs.Syntax
import SporkProofs.Notation
import SporkProofs.WFSyntax

def fibExample: Program :=
  PROGRAM (
    func main(
      block start() {n ← 10, CALL fib(n) ⊳ goto ret()},
      block ret(r) {RETURN(r)}
    ),
    func fib(
      block start(n) {SPORK (goto body(n), goto spwn(n))},
      block body(n) {n₁ ← n - 1, CALL fib(n₁) ⊳ goto cont(n)},
      block cont(n, r₁) {SPOIN (goto unpr(n, r₁), goto prom(r₁))},
      block unpr(n, r₁) {n₂ ← n - 2, CALL fib(n₂) ⊳ goto ret(r₁)},
      block prom(r₁, r₂) {GOTO ret(r₁,r₂)},
      block ret(r₁, r₂) {r ← r₁ + r₂, RETURN(r)},
      block spwn(n) {n₂ ← n - 2, CALL fib(n₂) ⊳ goto exit()},
      block exit(r₂) {RETURN(r₂)}
    )
  )

def parExample (f g : FuncIdx) : Func := func (
    block start() {SPORK (goto body(), goto spwn())},
    block body() {CALL f() ⊳ goto cont()},
    block cont(a) {SPOIN (goto unpr(a), goto prom(a))},
    block unpr(a) {CALL g() ⊳ goto ret(a)},
    block prom(r₁, r₂) {GOTO ret(r₁,r₂)},
    block ret(a, b) {RETURN(a,b)},
    block spwn() {CALL g() ⊳ goto exit()},
    block exit(b) {RETURN(b)}
  )

theorem parExampleWF : [⟨0, 1⟩, ⟨0, 1⟩] ⊢ (parExample 0 1) WF-func :=
  by decide

def reduceExample (f c reduce : FuncIdx) : Func := func (
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
    block left(z,i,m,j) {CALL reduce(z,z,i,m) ⊳ goto middle(z,m,j)},
    block middle(z,m,j,a) {SPOIN(goto leftover(z,m,j,a), goto merge(a))},
    block leftover(z,m,j,a) {CALL reduce(z,a,m,j) ⊳ goto exit()},
    block merge(a,a₁) {CALL c(a,a₁) ⊳ goto exit()},
    block exit(a) {RETURN(a)},
    block right(z,m,j) {CALL reduce(z,z,m,j) ⊳ goto exit()}
  )

-- set_option maxRecDepth 10000
theorem reduceExampleWF : [⟨1, 1⟩, ⟨2, 1⟩, ⟨4, 1⟩] ⊢ (reduceExample 0 1 2) WF-func :=
  by simp[reduceExample, Nat.repeat]; decide
