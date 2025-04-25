import Mathlib.Logic.Function.Defs
import Mathlib.Data.Real.Basic
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import LeanTestground.Basic



def add_invar_real_alt {a b:Real}(c:Real) : (a + c = b + c) -> a = b := by
  apply symm_fun_inj (f:=fun i => i + c)
  refine Subtype.mk ?_ ?_
  exact fun i => i - c
  simp only [add_sub_cancel_right, implies_true]

def add_invar_real {a b:Real}(c:Real) : (a + c = b + c) -> a = b := by
  let m := by
    refine @mkwmap Real Real ?_ ?_ ?_
    exact fun i => i + c
    exact fun i => i - c
    intro i
    exact add_sub_cancel_right i c

  apply wmap_inj m


def pow_invar_1 {a b c : Real} (h1: a >= 0)(h2: b >= 0)(h3:Not (c = 0)) : a ^ c = b ^ c -> a = b := by
  let _eq1 : wmap { i:Real // i >= 0 } { i:Real // i >= 0 } := by
    refine mkwmap ?_ ?_ ?_
    exact fun ⟨ i , p ⟩  => by
      refine ⟨ i ^ c , ?_ ⟩
      exact Real.rpow_nonneg p c
    exact fun ⟨ i , p ⟩ => by
      refine ⟨ i ^ (1 / c) , ?_ ⟩
      exact Real.rpow_nonneg p (1 / c)
    intro ⟨ i , p ⟩
    dsimp
    rw [@Subtype.mk_eq_mk]
    let eq1 : (i ^ c) ^ (1 / c) = i ^ (c * (1 / c)) := by
      refine Eq.symm (Real.rpow_mul ?_ c (1 / c))
      exact p
    rw [eq1]
    let eq3 : c * (1 / c) = 1 := by
      exact mul_one_div_cancel h3
    rw [eq3]
    norm_num
  let _eq2 := wmap_inj _eq1
  unfold Function.Injective _eq1 mkwmap at _eq2
  simp only [Subtype.forall, ge_iff_le, Subtype.mk.injEq] at _eq2
  let _eq2 := _eq2 a h1 b h2
  exact _eq2

def pow_invar_2 {a b c : Real} (h1: a >= 0)(h2: b >= 0)(h3:Not (c = 0)) : a ^ c = b ^ c <-> a = b := by
  apply Iff.intro
  exact fun a_1 => pow_invar_1 h1 h2 h3 a_1
  intro i
  rw [i]

def pows_to_mult {a b c:Real} (h1:a >= 0): (a ^ b) ^ c = a ^ (b * c) := by
  exact Eq.symm (Real.rpow_mul h1 b c)

def pow2_r {a b:Real} : (a * b) ^ (2:Real) = (a ^ 2) * (b ^ 2) := by
  rw [Real.rpow_two]
  exact mul_pow a b 2

def hmm : wmap { i // i = (Not P -> P)  } { i // i = (Not P -> False) } := by
  refine mkwmap ?_ ?_ ?_
  intro ⟨ r , p ⟩
  refine ⟨ r , ?_ ⟩
  rw [p]
  refine Eq.symm (implies_congr_ctx rfl ?_)
  exact fun a => Eq.symm (eq_false a)
  intro ⟨ r , p ⟩
  refine ⟨ r , ?_ ⟩
  rw [p]
  refine Eq.symm (implies_congr_ctx rfl ?_)
  exact fun a => eq_false a
  simp only [Subtype.coe_eta, implies_true]

-- -- cuberoot(7x) = sqrt(x) -> x = 49
-- set_option pp.proofs false in
example {x:Real}{xnz:x>=0} : (7 * x) ^ ((1:Real) / 3) = x ^ ((1:Real) / 2) -> x = 49 ∨ x = 0 := by
  let _eq1 := by
    refine pow_invar_2 (a:=(7 * x) ^ ((1:Real) / 3)) (b:=x ^ ((1:Real) / 2)) (c:=6) ?_ ?_ ?_
    {
      refine Real.rpow_nonneg ?_ (1 / 3)
      simp only [Nat.ofNat_pos, mul_nonneg_iff_of_pos_left]
      exact xnz
    }
    { exact Real.rpow_nonneg xnz (1 / 2)}
    { exact OfNat.ofNat_ne_zero 6 }
  rw [<- _eq1]
  clear _eq1
  rwi ((7 * x) ^ ((1:Real) / 3)) ^ (6:Real) => ((7 * x) ^ (6 * ((1:Real) / 3))) := by
    rw [@mul_one_div, pows_to_mult]
    norm_num
    norm_num
    exact xnz
  rewrite [pows_to_mult]
  ring_nf
  rewrite [pow2_r]
  ring_nf
  let _eq3 : (x ^ (2:Real) * 49 = x ^ (3:Real)) <-> ((x ^ (2:Real) * 49) - x ^ (3:Real) = 0) := by
    exact Iff.symm sub_eq_zero
  rw [← Real.rpow_two, _eq3]
  clear _eq3
  -- intro i
  -- by_contra ta
  -- let _eq_2 : Not (x = 49 ∨ x = 0) -> (Not (x = 49)) ∧ (Not (x = 0)) := by
  --   exact fun a => (fun {p q} => not_or.mp) ta
  -- let ⟨ c , _ ⟩ := _eq_2 ta
  -- clear _eq_2 ta
  let _eq : (x ^ (2:Real) * 49 - x ^ (3:Real) = 0) <-> (x ^ (2:Real) * (49 - x) = 0) := by
    refine eq_zero_iff_eq_zero_of_add_eq_zero ?_
    let _eq : (49:Real) - x = -x + 49 := by
      exact sub_eq_neg_add 49 x
    rw [_eq]
    let _eq2 : -x + 49 = -1 * (x - 49) := by
      norm_num
      rw [<-_eq]
    rw [_eq2]
    clear _eq2 _eq
    rwi x ^ (2:Real) * (-1 * (x - 49)) => -1 * (x ^ (2:Real) * (x - 49)) := by
      exact mul_left_comm (x ^ 2) (-1) (x - 49)
    rwi x ^ (2:Real) * 49 - x ^ (3:Real) => x ^ (2:Real) * (49 - x) := by
      refine Eq.symm (CancelDenoms.sub_subst rfl ?_)
      calc
        x^(2 : ℝ) * x = x^(2 + 1 : ℝ) := by rw [Real.rpow_two]; norm_cast
        _ = x^(3 : ℝ) := by norm_num
    rwi -1 * (x ^ (2:Real) * (x - 49)) => x ^ (2:Real) * (-1 * (x - 49)) := by
      exact mul_left_comm (-1) (x ^ 2) (x - 49)
    rwi x ^ (2:Real) * (49 - x) + x ^ (2:Real) * (-1 * (x - 49)) => x ^ (2:Real) * ((49 - x) + (-1 * (x - 49))) := by
      exact Eq.symm (LeftDistribClass.left_distrib (x ^ 2) (49 - x) (-1 * (x - 49)))
    rwi -1 * (x - 49) => -x + 49 := by norm_num; exact sub_eq_neg_add 49 x
    rwi 49 - x => -x + 49 := by exact sub_eq_neg_add 49 x
    rwi -x + 49 + (-x + 49) => 2 * (-x + 49) := by exact Eq.symm (two_mul (-x + 49))
    rwi 2 * (-x + 49) => -2 * x + 98 := by ring_nf
    let _roots : x ^ 2 = 0 ∨ -2 * x + 98 = 0 -> x ^ (2:Real) * (-2 * x + 98) = 0 := by norm_num
    apply _roots
    clear _roots
    refine .inr ?_
    rwi -2 * x + 98 = 0 => -2 * x = -98 := by
      apply propext
      exact Iff.symm eq_neg_iff_add_eq_zero
    rwi -2 * x = -98 => x = -98 / -2 := by
      norm_num
      refine Function.Injective.eq_iff' ?_ ?_
      unfold Function.Injective
      intro a b
      let eq : wmap Real Real := by
        refine mkwmap ?_ ?_ ?_
        exact fun i => i * 2
        exact fun i => i / 2
        intro i
        ring_nf
      let _eq := wmap_inj eq
      unfold Function.Injective eq mkwmap at _eq
      simp only [OfNat.ofNat_ne_zero, or_false ] at _eq
      rw [NonUnitalNormedCommRing.mul_comm 2 a, NonUnitalNormedCommRing.mul_comm 2 b]
      apply _eq
      ring_nf
    ring_nf
    admit
  rw [_eq]
  clear _eq
  intro h
  rw [mul_eq_zero] at h
  cases h
  case _ h =>
    refine .inr ?_
    let eq := by
      refine pow_invar_2 (a:= x ^ (2:Real)) (b:=0) (c:=(1:Real)/2) ?_ ?_ ?_
      exact Real.rpow_nonneg xnz 2
      exact Preorder.le_refl 0
      simp only [one_div, inv_eq_zero, OfNat.ofNat_ne_zero, not_false_eq_true]
    rw [<-eq] at h
    clear eq
    rwi ((x ^ (2:Real)) ^ ((1:Real) / 2) = 0 ^ ((1:Real) / 2)) => (x = 0) at h := by
      rwi (x ^ (2:Real)) ^ ((1:Real) / 2) => x ^ (2 * ((1:Real)/2)) := by
        exact pows_to_mult xnz
      rwi (2 * ((1:Real) / 2)) => 1 := by
        norm_num
      rwi (x ^ (1:Real)) => x := by
        exact Real.rpow_one x
      rwi (0:Real) ^ ((1:Real) / 2) => 0 := by
        refine Real.zero_rpow ?_
        norm_num
      rfl
    exact h
  case _ h =>
    refine .inl ?_
    rwi 49 - x = 0 => - x = -49 at h := by
      rwi 49 - x => -x + 49 := by
        exact sub_eq_neg_add 49 x
      apply propext
      apply Iff.intro
      intro i
      exact Eq.symm (neg_eq_of_add_eq_zero_right h)
      intro i
      exact eq_neg_iff_add_eq_zero.mp i
    rwi -x = -49 => x = 49 at h := by
      apply propext
      exact neg_inj
    exact h
  exact xnz



def real_to_nat : wmap ((r:Real) × { i:Int // r = i }) Int := by
  refine mkwmap ?_ ?_ ?_
  intro ⟨ r , ⟨ i , p ⟩ ⟩
  exact i
  intro i
  refine ⟨ i.cast , ?_ ⟩
  simp only [Int.cast_inj]
  exact ⟨i, rfl⟩
  intro ⟨ n , ⟨ k , j ⟩ ⟩
  simp only [eq_mpr_eq_cast, Sigma.mk.inj_iff, cast_heq_iff_heq]
  apply And.intro
  exact Eq.symm j
  cases j
  refine (Subtype.heq_iff_coe_eq ?_).mpr rfl
  exact fun x => Iff.symm Int.cast_inj

def real_to_rat : wmap ((r:Real) × { i:Rat // r = i }) Rat := by
  refine mkwmap ?_to ?_from ?_coh
  {
    intro ⟨ r , i , p ⟩
    exact i
  }
  {
    intro i
    refine .mk i.cast (.mk i ?_)
    rfl
  }
  intro ⟨ r, i, p ⟩
  dsimp
  subst p
  rfl




example : is_contr { i:Int // n1 = i } := by
  unfold is_contr
  refine ⟨ ⟨ n1 , rfl ⟩ , ?_ ⟩
  intro ⟨ k , p ⟩
  subst p
  rfl

-- def f (a : Bool) : Prop := a

-- def h (_ : Bool) : Prop := True

theorem cast_injective {α β} (h : α = β) {a b} : cast h a = cast h b → a = b := by
  subst h
  exact id

-- theorem neq : ¬ {a : Bool // h a} = {a : Bool // f a} := by
--   intro x
--   let a : {a : Bool // h a} := ⟨false, trivial⟩
--   let b : {a : Bool // h a} := ⟨true, trivial⟩
--   let xa := @Eq.rec Type { a // h a } (fun x h => x) a { a // f a } x
--   let xb := @Eq.rec Type { a // h a } (fun x h => x) b { a // f a } x
--   let tmp2 := Eq.trans xa.2 xb.2.symm
--   let tmp1 := Subtype.ext tmp2
--   have := cast_injective x tmp1
--   simp only [Subtype.mk.injEq, Bool.false_eq_true, a, b] at this



-- set_option pp.proofs true in
-- theorem thm : False := by
--   let k1 := (heq_mk_inj_iff (f := f) (h := h) (a1 := true) (a2 := true) (b1 := rfl) (b2 := trivial))
--   let k2 := k1.mpr (by simp [proof_irrel_heq])
--   let k3 := (type_eq_of_heq k2).symm

--   let _ := neq k3
--   assumption



-- theorem neq_2 : ¬ {a : Bool // h a} = {a : Bool // f a} := by
--   intro x
--   let a : {a : Bool // h a} := ⟨false, trivial⟩
--   let b : {a : Bool // h a} := ⟨true, trivial⟩
--   have := cast_injective x (Subtype.ext ((x ▸ a).2.trans (x ▸ b).2.symm))
--   simp [a, b] at this

-- theorem thm_2 : False :=
--   neq_2 (heq_mk_inj_iff (f := f) (h := h) (a1 := true) (a2 := true) (b1 := rfl) (b2 := trivial) |>.mpr (by simp [proof_irrel_heq]) |> type_eq_of_heq).symm

-- #print axioms thm_2

inductive Proper (P:Prop) : Type | mk (p:P)

def wmap_prop: Sort _ -> Sort _ -> Sort _ | A, B => @Subtype (And (A -> B) (B -> A)) fun ⟨ f , h ⟩ => ∀ i, h (f i) = i

set_option pp.proofs true in
def p1_prop : (w:wmap_prop A B) -> ∀ a:A , @Subtype B fun b => w.val.right b = a := by
  intro w
  let ⟨ ⟨ f , h ⟩ , p ⟩ := w
  dsimp at p
  dsimp
  intro a
  refine ⟨ f a , ?_ ⟩
  dsimp

def mkwmap_prop (f: A -> B)(h:B->A)(p: ∀ i, h (f i) = i) : wmap_prop A B := ⟨ ⟨ f , h ⟩  , p ⟩

@[simp]
def and_right_to_val : (⟨ a , b ⟩:And _ _).right = b := by
  rfl

def proj_inj {f h:A->Prop}{p1:f a}{p2:h b}: a = b -> Subtype.val (Subtype.mk a p1) = Subtype.val (Subtype.mk b p2) := by
  intro p
  cases p
  rfl

def proj_inj_2 {f h:A->Prop}{p1:f a}{p2:h b}: a = b -> Subtype.val (Subtype.mk a p1) = Subtype.val (Subtype.mk b p2) := by
  intro p
  cases p
  rfl

def only_refl {a b:A}: ∀ (q:a=b), q = (by subst q; exact .refl _) := by
  intro q
  cases q
  rfl

def cast_reorder {f:A->B}: cast rfl (f a) = f (cast rfl a) := by
  exact rfl

set_option pp.proofs true in
def cast_proj_1_eq_proj_cast {f h:A->Prop}{b:f a}{eq:{ i:A // f i } = { i:A // h i }}: (cast eq ⟨ a , b ⟩).val = cast rfl ((⟨ a , b ⟩:Subtype _).val) := by
  -- rw [cast_eq]
  -- apply proj_inj
  -- repeat rw [@eqRec_eq_cast]
  -- rw [eq_rec_constant eq rfl]
  -- rw [only_refl eq]
  -- rw [eq_mpr_eq_cast (congrFun (congrArg Eq eq) { i // h i })]
  rw [cast_reorder]
  rw [only_refl eq]
  refine (Subtype.heq_iff_coe_eq ?_).mp ?_
  {
    admit
  }
  {
    simp only [cast_eq, cast_heq]
  }

set_option pp.proofs true in
def reduce_cast_subtype_proj_1_ {A : Type} {v1 : A} {p1 p2 : A → Prop} {k1 : p1 v1} (eq : {i // p1 i} = {i // p2 i}) :
  (cast eq ⟨v1, k1⟩).val = v1
:= by
  rw [cast_proj_1_eq_proj_cast]
  rw [cast_eq]

axiom reduce_cast_subtype_proj_1 {A:Type}{v1:A}{p1 p2:A->Prop}{k1: p1 v1}(eq:{ i // p1 i } = { i // p2 i }):
  (@cast { i // p1 i } { i // p2 i } (eq) ⟨v1, k1⟩).val = v1

set_option pp.proofs true in
def heq_to (eq1:A=B)(k1:@HEq A a B b):@HEq A a A (by subst eq1; exact b) := by
  simp only [heq_eq_eq]
  rw [@eqRec_eq_cast]
  cases eq1
  simp only [cast_eq]
  rw [<-heq_eq_eq]
  exact k1

def heq_from (eq1:A=B)(k1:@HEq A a A (by subst eq1; exact b)): @HEq A a B b := by
  simp only [heq_eq_eq] at k1
  rw [@eqRec_eq_cast] at k1
  cases eq1
  simp only [cast_eq] at k1
  rw [<-heq_eq_eq] at k1
  exact k1

def heq_heq (eq1:A=B): (@HEq A a A (by subst eq1; exact b)) = (@HEq A a B b) := by
  apply propext
  apply Iff.intro
  exact heq_from eq1
  intro i
  cases eq1
  simp only [heq_eq_eq]
  rw [heq_eq_eq] at i
  exact i

def subtype_val_eq {f:A->Prop}{p1:f a1}{p2:f a2}(p1:(Subtype.mk a1 p1) = (Subtype.mk a2 p2)): a1 = a2 := by
  cases p1
  rfl

set_option pp.proofs true in
def unstuck_rec {A: Type _}{B:Type _}(eq:Eq A B){val:B}
: (@Eq.rec Type
    A (fun x _ => {_ : x} → A) (fun {b} => b) B
    eq
    val) = (by rw [eq]; exact val)
:= by
  reduce
  cases eq
  rfl

set_option pp.proofs true in
def heq_subtype_to_eq_val
  {A:Type}{n1 n2:A}
  {p1 p2:A->Prop}{k1: p1 n1}{k2: p2 n2}
  (eq: @HEq { i // p1 i } ⟨n1, k1⟩ { i // p2 i } ⟨n2, k2⟩)
: n1 = n2
:= by
  let t_eq := type_eq_of_heq eq
  rw [<- (heq_heq t_eq)] at eq
  simp only [heq_eq_eq] at eq
  let eq2 := subtype_val_eq eq
  rw [unstuck_rec] at eq2
  simp at eq2
  rw [@reduce_cast_subtype_proj_1] at eq2
  exact eq2

#print axioms heq_subtype_to_eq_val

set_option pp.proofs true in
-- set_option diagnostics true in
example {n:Real}{nnlz:n >= 0}: (n ^ ((1:Real) / 2) ) ^ (2:Real) = n := by

  rwi (n ^ ((1:Real) / 2)) ^ (2:Real) => n ^ (((1:Real) / 2) * 2) := by
    exact Eq.symm (Real.rpow_mul nnlz _ _)

  generalize _re1: (2:Real) = V
  let w := by
    refine transp real_to_rat (.mk V (.mk 2 ?_))
    exact (Eq.symm _re1)
  let (.mk n1 p) := w
  dsimp only [eq_mpr_eq_cast, id_eq, cast_eq] at p
  unfold real_to_rat mkwmap at p
  simp only [Sigma.mk.inj_iff] at p
  let ⟨ eq1 , eq2 ⟩ := p
  let eq2 := heq_subtype_to_eq_val eq2
  rw [eq2] at eq1
  rw [<-eq1]

  generalize _re2: (1:Real) = V
  let w := by
    refine transp real_to_rat (.mk V (.mk 1 ?_))
    rw [<-_re2]
    exact Eq.symm Rat.cast_one
  let (.mk n1 p) := w
  dsimp only [eq_mpr_eq_cast, id_eq, cast_eq] at p
  unfold real_to_rat mkwmap at p
  simp only [Sigma.mk.inj_iff, cast_heq_iff_heq] at p
  let ⟨ eq1 , eq2 ⟩ := p
  let eq2 := heq_subtype_to_eq_val eq2
  rw [eq2] at eq1
  rw [<-eq1]

  rwi (((↑(1:Rat)):Real) / ↑(2:Rat)) => ↑((1:Rat) / 2) := by
    exact Eq.symm (Rat.cast_div 1 2)

  rwi ((↑(1 / (2:Rat))):Real) * ↑(2:Rat) => ↑((1/(2:Rat))*2) := by
    exact Eq.symm (Rat.cast_mul (1 / 2) 2)

  rwi 1 / (2:Rat) * 2 => 1 := by
    exact div_mul_cancel_of_invertible 1 2

  simp only [Rat.cast_one, Real.rpow_one]


set_option pp.proofs true in
def heq_subtype_to_eq_
  {A:Type}{n1 n2:A}
  {p1 p2:A->Prop}{k1: p1 n1}{k2: p2 n2}
  (prop_eq:p1 = p2)
  (eq: @HEq { i // p1 i } ⟨n1, k1⟩ { i // p2 i } ⟨n2, k2⟩)
: n1 = n2 ∧ HEq (k1) (k2)
:= by
  apply And.intro
  {
    let t_eq := type_eq_of_heq eq
    subst prop_eq
    cases eq
    rfl
  }
  {
    exact proof_irrel_heq k1 k2
  }



set_option pp.proofs true in
def heq_subtype_to_eq
  {A:Type}{n1 n2:A}
  {p1 p2:A->Prop}{k1: p1 n1}{k2: p2 n2}
  (eq: @HEq { i // p1 i } ⟨n1, k1⟩ { i // p2 i } ⟨n2, k2⟩)
: n1 = n2 ∧ HEq (k1) (k2)
:= by
  apply And.intro
  {
    let t_eq := type_eq_of_heq eq
    rw [<- (heq_heq t_eq)] at eq
    simp only [heq_eq_eq] at eq
    let eq2 := subtype_val_eq eq
    rw [unstuck_rec] at eq2
    rw [eq_mpr_eq_cast] at eq2
    rw [id.eq_1 t_eq] at eq2
    rw [reduce_cast_subtype_proj_1] at eq2
    exact eq2
  }
  {
    exact proof_irrel_heq k1 k2
  }

-- theorem eq_rec_eq_ndrec {α : Type} {a b : α} (h : a = b) (c : α) :
--   Eq.rec (motive := fun x _ => α) c h = Eq.ndrec c h := by
--   -- Since the motive is constant (α), Eq.rec and Eq.ndrec are definitionally the same.
--   rfl

-- example {A:Type}{v1:A}{p1 p2:A->Prop}{k1: p1 v1}{k2: p2 v1}(eq:{ i // p1 i } = { i // p2 i })
-- : (@cast { i // p1 i } { i // p2 i } (eq) ⟨v1, k1⟩).val = (Subtype.mk v1 k2).val
-- := by
--   generalize eq1 : cast eq ⟨v1, k1⟩ = cv
--   let _ : (cast eq ⟨v1, k1⟩).val = (Subtype.mk v1 k2).val := by
--     apply congrArg
--     rw?
--     admit
--   done

set_option pp.proofs true in
def heq_subtype_to_eq_2
  {A:Type}{n1 n2:A}
  {p1 p2:A->Prop}{k1: p1 n1}{k2: p2 n2}
  (eq: @HEq { i // p1 i } ⟨n1, k1⟩ { i // p2 i } ⟨n2, k2⟩)
: n1 = n2 ∧ HEq (k1) (k2)
:= by
  apply And.intro
  {
    let t_eq := type_eq_of_heq eq
    rw [← propext (cast_eq_iff_heq (e:=t_eq))] at eq
    rw [@Subtype.ext_iff_val] at eq
    rw [@cast_proj_1_eq_proj_cast] at eq
    simp at eq
    exact eq
    -- rw [<- (heq_heq t_eq)] at eq
    -- rw [rec_is_ndrec]
    -- -- rw [heq_cast_iff_heq] at eq
    -- simp only [heq_eq_eq] at eq
    -- let eq2 := subtype_val_eq eq
    -- rw [unstuck_rec] at eq2
    -- rw [eq_mpr_eq_cast] at eq2

    -- rw [id.eq_1 t_eq] at eq2
    -- rw [reduce_cast_subtype_proj_1] at eq2
    -- exact eq2
  }
  {
    exact proof_irrel_heq k1 k2
  }

-- set_option pp.proofs true in
-- def heq_subtype_to_eq_2
--   {A:Type}{n1 n2:A}
--   {p1 p2:A->Prop}{k1: p1 n1}{k2: p2 n2}
--   (eq:n1 = n2 ∧ HEq (k1) (k2))
-- : @HEq { i // p1 i } ⟨n1, k1⟩ { i // p2 i } ⟨n2, k2⟩
-- := by
--   let ⟨ x , k ⟩ := eq
--   cases x

set_option pp.proofs true in
-- set_option diagnostics true in
example {n:Real}{nnlz:n >= 0}: (n ^ ((1:Real) / 2) ) ^ (2:Real) = n := by

  rwi (n ^ ((1:Real) / 2)) ^ (2:Real) => n ^ (((1:Real) / 2) * 2) := by
    exact Eq.symm (Real.rpow_mul nnlz _ _)

  generalize _re1: (2:Real) = V
  let w := by
    refine transp real_to_rat (.mk V (.mk 2 ?_))
    exact (Eq.symm _re1)
  let (.mk n1 p) := w
  dsimp only [eq_mpr_eq_cast, id_eq, cast_eq] at p
  unfold real_to_rat mkwmap at p
  simp only [Sigma.mk.inj_iff] at p
  let ⟨ eq1 , eq2 ⟩ := p
  let eq2 := by
    refine heq_subtype_to_eq_ ?_ eq2
    funext i
    rw [eq1]
  rw [eq2.left] at eq1
  rw [<-eq1]

  generalize _re2: (1:Real) = V
  let w := by
    refine transp real_to_rat (.mk V (.mk 1 ?_))
    rw [<-_re2]
    exact Eq.symm Rat.cast_one
  let (.mk n1 p) := w
  dsimp only [eq_mpr_eq_cast, id_eq, cast_eq] at p
  unfold real_to_rat mkwmap at p
  simp only [Sigma.mk.inj_iff, cast_heq_iff_heq] at p
  let ⟨ eq1 , eq2 ⟩ := p
  let eq2 := by
    refine heq_subtype_to_eq_ ?_ eq2
    funext i
    rw [eq1]
  rw [eq2.left] at eq1
  rw [<-eq1]

  rwi (((↑(1:Rat)):Real) / ↑(2:Rat)) => ↑((1:Rat) / 2) := by
    exact Eq.symm (Rat.cast_div 1 2)

  rwi ((↑(1 / (2:Rat))):Real) * ↑(2:Rat) => ↑((1/(2:Rat))*2) := by
    exact Eq.symm (Rat.cast_mul (1 / 2) 2)

  rwi 1 / (2:Rat) * 2 => 1 := by
    exact div_mul_cancel_of_invertible 1 2

  simp only [Rat.cast_one, Real.rpow_one]
