import SporkProofs.Syntax
import SporkProofs.Notation
import SporkProofs.WFSyntax

/-!
Implementation of `par` and `reduce` in Spork IR,
along with proofs of their well-formedness.

We use the DSL notation for Spork IR defined in `SporkProofs.Notation`
-/


def par (f g : FuncIdx) : Func := func (
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

def reduce (f c reduce : FuncIdx) : Func := func (
    block start(z,a,i,j):
      GOTO guard(z,i,j,a)
    block guard(z,i,j,a):
      b ← i >= j,
      IF b THEN goto done(a) ELSE goto iter(z,i,j,a)
    block done(a):
      RETURN(a)
    block iter(z,i,j,a):
      SPORK (goto body(z,i,j,a), goto split(z,i,j,a))
    block body(z,i,j,a):
      CALL f(i) ⊳ goto accum(z,i,j,a)
    block accum(z,i,j,a,a₁):
      CALL c(a,a₁) ⊳ goto cont(z,i,j)
    block cont(z,i,j,a):
      SPOIN (goto next(z,i,j,a), goto brk(a))
    block next(z,i,j,a):
      i₁ ← i + 1,
      GOTO guard(z,i₁,j,a)
    block brk(a,a₁):
      CALL c(a,a₁) ⊳ goto done()
    block split(z,i,j,a):
      i₁ ← i + 1,
      k ← i₁ + j,
      m ← k / 2,
      SPORK (goto left(z,i₁,m,j), goto right(z,m,j))
    block left(z,i,m,j):
      CALL reduce(z,z,i,m) ⊳ goto middle(z,m,j)
    block middle(z,m,j,a):
      SPOIN(goto leftover(z,m,j,a), goto merge(a))
    block leftover(z,m,j,a):
      CALL reduce(z,a,m,j) ⊳ goto exit()
    block merge(a,a₁):
      CALL c(a,a₁) ⊳ goto exit()
    block exit(a):
      RETURN(a)
    block right(z,m,j):
      CALL reduce(z,z,m,j) ⊳ goto exit()
  )

/--
  [⟨0, 1⟩, ⟨0, 1⟩] => [f takes 0 args and returns 1, g takes 0 args and returns 1]
  par 0 1 => par (func idx 0 = f, func idx 1 = g)
-/
theorem parWF : [⟨0, 1⟩, ⟨0, 1⟩] ⊢ (par 0 1) WF-func :=
  by decide

/--
[⟨1, 1⟩, ⟨2, 1⟩, ⟨4, 1⟩] =>
  [f takes 1 arg and returns 1,
   c(ombine) takes 2 args and returns 1,
   reduce (needed for recursive calls) takes 4 args and returns 1]

reduce 0 1 2 => reduce (func idx 0 = f, func idx 1 = c, func idx 2 = reduce)

this nearly reaches the default max recursion depth,
if you get an error about it, increase the limit:
`set_option maxRecDepth 10000`
-/
theorem reduceWF : [⟨1, 1⟩, ⟨2, 1⟩, ⟨4, 1⟩] ⊢ (reduce 0 1 2) WF-func :=
  by simp[reduce, Nat.repeat]; decide
