import Mathlib


macro "rwi" pat:term "=>" new:term "at" loc:Lean.Parser.Tactic.locationHyp ":=" prf:term : tactic =>
  `(tactic| rewrite [let _eq : $pat = $new := $prf ; _eq ] at $loc)

macro "rwi" pat:term "=>" new:term ":=" prf:term : tactic =>
  `(tactic| rewrite [let _eq : $pat = $new := $prf ; _eq ])

-- inductive Eq_ : {A:Type _} -> {B:Type _} -> A -> B -> Type _ | refl : {A:Type _} -> {a:A} -> Eq_ a a

def iscontr (T:Type _):Prop := ∀ (a b:T), a = b

def wmap {A: Type _}{B:Type _}(f:A->B): Type _ := @Subtype (B -> A) fun h => ∀ i, h (f i) = i

def mkwmap (f: A -> B)(h:B->A)(p: ∀ i, h (f i) = i) : wmap f := ⟨ h , p ⟩

def eq_canon3 {a:A}{b:B} : ∀ (p:HEq a b), HEq p (HEq.refl a) := by
  intro (.refl _)
  exact (.refl _)

def Eq.to_heq (this:a = b) : HEq a b := by
  let (.refl _) := this
  exact (.refl _)

def id_fun : (∀ i, f i = i) -> f = id := by
  intro eq
  funext k
  rw [eq]
  simp only [id_eq]

set_option pp.proofs true in
example : iscontr (wmap (@id T)) := by
  intro ⟨ h1, p1 ⟩  ⟨ h2 , p2 ⟩
  simp only [id_eq] at p1 p2
  let e1 : h1 = id := id_fun p1
  let e2 : h2 = id := id_fun p2
  simp only [e1, e2]


def no_funcs : iscontr A -> iscontr (A -> A) := by
  unfold iscontr
  intro i f h
  rwi f => h := by
    funext p
    rw [(i (f p) (h p))]
  rfl


-- def no_funcs_ {P:A->Type _}: iscontr A -> iscontr ((i:A) -> P i) := by
--   unfold iscontr
--   intro i f h
--   rwi f => h := by
--     funext p
--     let _ :=
--   exact .refl

#check cast_eq


set_option pp.proofs true in
def all_to_exist_on_contr {A:Type _}{P:A->Type _}{i:A}: iscontr A -> @wmap ((i:A) -> P i) (P i) (fun k => k i) := by
  unfold iscontr
  intro a1
  refine mkwmap ?_ ?_ ?_
  intro a z
  let k := (a1 i z)
  rw [k] at a
  exact a
  simp only [eq_mp_eq_cast]
  intro m
  apply funext
  intro v
  let k := (a1 i v)
  rw [← cast_cast rfl (congrArg P k) (m i), cast_eq]
  let x : P i = P v := congrArg P k
  let _ := @cast (P i) (P v) x (m i)
  cases k
  rfl


def unit_contr : iscontr Unit := by
  intro (.unit) (.unit)
  rfl

inductive Proper (P:Prop) : Type | mk (p:P)

def _prf : ∀ i:Bool, not i = not (not (not i)) := by exact fun i => Eq.symm (Bool.not_not !i)

def shift (w: @wmap A B f): ∀ i, { k // i = (w.val k) } := by
  intro i
  let ⟨ h, p ⟩ := w
  dsimp
  refine ⟨ (f i) , ?_ ⟩
  rw [p]


example : ∀ i:Bool, i = not (not i) := by
  intro i
  let x := mkwmap (not) not (by exact fun i => Bool.not_not i)
  let k := shift x i
  unfold x mkwmap at k; simp at k
  let ⟨ v, p ⟩ := k
  rw [p]
  apply _prf


example {A:Type _}{B:Type _}{f:A->B}{h:B->A}{p:∀ i, h (f i) = i}: ∀ (a:A), { b // a = h b } := by
  intro a
  refine .mk ?_ ?_
  exact f a
  rw [p a]

def wmap_alt (A:Type _)(B:Type _): Type _ := @Subtype ((A->B) × (B->A)) fun (inj , prj) => ∀ i, prj (inj i) = i

def wmap_alt_wmap : (w:wmap_alt A B) -> wmap w.val.fst := by
  intro w
  let ⟨ (f, h) , p ⟩ := w
  simp at p
  simp
  refine .mk ?_ ?_
  exact h
  exact p

def iso (A:Type _)(B:Type _){f:A->B}: Prop := iscontr (@wmap A B f)

example {f} : iso A B (f:=f) := by
  unfold iso iscontr wmap
  intro ⟨ prj1 , p1 ⟩ ⟨ prj2 , p2 ⟩

  admit

def _p1 {w:wmap_alt A A}: Function.Injective w.val.fst := by
  let ⟨ (f, h) , p ⟩  := w
  exact Function.LeftInverse.injective p

def _p2 {w:wmap_alt A A}: Function.Surjective w.val.snd := by
  let ⟨ (f, h) , p ⟩  := w
  exact Function.RightInverse.surjective p

-- set_option pp.proofs true in
-- def all_to_exist_on_contr {A:Type _}{P:A->Type _}{i:A}: iscontr A -> @wmap_alt ((i:A) -> P i) (P i) (fun k => k i) := by



-- example {a:Real}: (a^(4:Real)) ^ ((1:Real)/3) = a * (a ^ (1:Real)/3) := by
--   rwi (a ^ (4:Real)) ^ ((1:Real) / 3) => a ^ ((4:Real) * (1:Real)/3) := by
--     ring_nf


-- example {n a b :Real} : (n ^ a) ^ b = n ^ (a * b):= by
--   refine Eq.symm (Real.rpow_mul ?_ a b)

#reduce 1 + 250 * 251^0 + 250 * 251^1 + 250 * 251^2 + 250 * 251^3 + 250 * 251^4 + 250 * 251^5 + 250 * 251^6 + 250 * 251^7
