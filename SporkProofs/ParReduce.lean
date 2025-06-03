import SporkProofs.Syntax

-- start(): spork(body(), g())
-- body(): call f() ⊳ cont(·)
-- cont(x): spoin(unpr(x), prom(x, ·))
-- unpr(x): call g() ⊳ ret(x, ·)
-- prom(x, y): goto ret(x, y)
-- ret(x, y): return(x,y)

def parSSA : Function [⟨0,1⟩, ⟨0,1⟩, ⟨0,2⟩] ⟨0,2⟩ :=
  let f : Var 3 := 0
  let g : Var 3 := 1
  func (
    bb start() {SPORK 1 (goto body(), g())},
    bb body() sporks (1) {CALL f() ⊳ goto cont()},
    bb cont(x) sporks (1) {SPOIN (goto unpr(x), goto prom(x))},
    bb unpr(x) {CALL g() ⊳ goto ret(x)},
    bb prom(x, y) {GOTO ret(x,y)},
    bb ret(x, y) {RETURN(x, y)}
  )

-- reduce(z,a,i,j) -> a₁
--   start(z,a,i,j): goto guard(z,i,j,a)
--   guard(z,i,j,a): b ← i ≥ j; if b then done(a) else iter(z,i,j,a)
--   done(a): return(a)
--   iter(z,i,j,a): spork(body(z,i,j,a), split(z,i,j,a))
--   body(z,i,j,a): call f(i) ⊳ accum(z,i,j,a,·)
--   accum(z,i,j,a,a₁): call c(a,a₁) ⊳ cont(z,i,j,·)
--   cont(z,i,j,a): spoin(next(z,i,j,a), break(a,·))
--   next(z,i,j,a): i₁ ← i + 1; goto guard(z,i₁,j,a)
--   break(a,a₁): call c(a,a₁) ⊳ done(·)

-- split(z,a,i,j) -> a₁
--   spwn(z,a,i,j): i₁ ← i + 1; k ← i₁ + j; m ← k / 2; spork(left(z,i₁,m), reduce(z,z,m,j))
--   left(z,i,m): call reduce(z,z,i,m) ⊳ middle(z,m,j,·)
--   middle(z,m,j,a): spoin(leftover(z,m,j,a), join(a,·))
--   leftover(z,m,j,a): call reduce(z,a,m,j) ⊳ exit(·)
--   join(a,a₁): call c(a,a₁) ⊳ exit(·)
--   exit(a): return(a)

def redSSA : Function [⟨2,1⟩, ⟨1,1⟩, ⟨4,1⟩, ⟨4,1⟩] ⟨4,1⟩ × Function [⟨2,1⟩, ⟨1,1⟩, ⟨4,1⟩, ⟨4,1⟩] ⟨4,1⟩ :=
  let     c : Var 4 := 0
  let     f : Var 4 := 1
  let   red : Var 4 := 2
  let split : Var 4 := 3
  (func (
     bb start(z,a,i,j) {GOTO guard(z,i,j,a)},
     bb guard(z,i,j,a) {b ← i >= j, IF b THEN goto done(a) ELSE goto iter(z,i,j,a)},
     bb done(a) {RETURN(a)},
     bb iter(z,i,j,a) {SPORK 1 (goto body(z,i,j,a), split(z,i,j,a))},
     bb body(z,i,j,a) sporks (1) {CALL f(i) ⊳ goto accum(z,i,j,a)},
     bb accum(z,i,j,a,a₁) sporks (1) {CALL c(a,a₁) ⊳ goto cont(z,i,j)},
     bb cont(z,i,j,a) sporks (1) {SPOIN (goto next(z,i,j,a), goto brk(a))},
     bb next(z,i,j,a) {i₁ ← i + 1, GOTO guard(z,i₁,j,a)},
     bb brk(a,a₁) {CALL c(a,a₁) ⊳ goto done()}
   ),
   func (
     bb spwn(z,a,i,j) {i₁ ← i + 1, k ← i₁ + j, m ← k / 2, SPORK 1 (goto left(z,i₁,m,j), red(z,z,m,j))},
     bb left(z,i,m,j) sporks (1) {CALL red(z,z,i,m) ⊳ goto middle(z,m,j)},
     bb middle(z,m,j,a) sporks (1) {SPOIN(goto leftover(z,m,j,a), goto join(a))},
     bb leftover(z,m,j,a) {CALL red(z,a,m,j) ⊳ goto exit()},
     bb join(a,a₁) {CALL c(a,a₁) ⊳ goto exit()},
     bb exit(a) {RETURN(a)}
   ))  
