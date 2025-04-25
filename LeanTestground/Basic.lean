
import Mathlib.Data.Rat.Defs
import Mathlib.Logic.Function.Defs
import Batteries.Data.Rat.Basic
import Mathlib.Algebra.Group.Basic
-- import Mathlib.Order.Basic

macro "rwi" pat:term "=>" new:term ":=" prf:term : tactic =>
  `(tactic| rewrite [let _eq : $pat = $new := $prf ; _eq ])

macro "rwi" pat:term "=>" new:term "at" loc:Lean.Parser.Tactic.locationHyp ":=" prf:term : tactic =>
  `(tactic| rewrite [let _eq : $pat = $new := $prf ; _eq ] at $loc)

def wmap : Sort _ -> Sort _ -> Sort _ | A, B => @Subtype ((A -> B) ×' (B -> A)) fun ⟨ f , h ⟩ => ∀ i, h (f i) = i

def transp : (w:wmap A B) -> ∀ a:A , @Subtype B fun b => w.val.snd b = a := by
  intro w
  let ⟨ ⟨ f , h ⟩ , p ⟩ := w
  simp at p
  simp
  intro a
  refine ⟨ f a , ?_ ⟩
  apply p


def mkwmap (f: A->B)(h:B->A)(p: ∀ i, h (f i) = i) : wmap A B := ⟨ ⟨ f , h ⟩  , p ⟩

def wmap_inj (w:wmap A B) : Function.Injective w.val.fst := by
  let ⟨ _ , p ⟩ := w;
  exact Function.LeftInverse.injective p

def wmap_sur (w:wmap A B) : Function.Surjective w.val.snd := by
  let ⟨ _ , p ⟩ := w;
  exact Function.RightInverse.surjective p


example :∀ (c:Rat), Function.Injective (fun (i:Rat) => i + c) := by
  intros c
  let prf : wmap Rat Rat := by
    refine mkwmap ?_ ?_ ?_
    exact fun i => i + c
    exact fun i => i - c
    intro i
    rwi (i + c) - c => (c + i) - c := by
      refine sub_left_inj.mpr ?_
      exact Rat.add_comm i c
    rwi (c + i) - c => (c - c) + i := by
      exact add_sub_right_comm c i c
    rwi c - c => 0 := by exact sub_eq_zero_of_eq rfl
    rwi 0 + i => i := by exact Rat.zero_add i
    rfl
  exact wmap_inj prf


example {x:Nat} (h1:x = 2)(h2:x = 3): 2 = 3 := by
  rw [h1] at h2
  exact h2

example {x:Nat} (h1:x = 2)(h2:x = 3): 2 = 3 := by
  rw [h1] at h2
  by_contra k
  exact k h2



-- example {a c b :Rat}{f:Rat->Rat} (k:Function.Injective f) : f a >= f b -> a >= b := by
--   intro a_1
--   simp_all only [ge_iff_le]

-- example {x:Rat}: 2*(0.4 + x) - 2.8 >= 2.3 + 3 * x -> x <= -4.3 := by
--   rwi 2 * (0.4 + x) => 0.8 + (2 * x) := by ring
--   rwi 0.8 + 2 * x - 2.8 => (0.8 - 2.8) + 2 * x := by
--     exact add_sub_right_comm 0.8 (2 * x) 2.8
--   rwi (0.8:Rat) - 2.8 => - 2 := by ring
--   rwi (-2 + 2 * x ≥ 2.3 + 3 * x) => (2.3 + 3 * x <= -2 + 2 * x) := by rfl

--   -- let _ : (-2 + 2 * x ≥ 2.3 + 3 * x) = ((-2 + 2 * x) - (3 * x) ≥ (2.3 + 3 * x) - (3 * x)) := by

example {f:A->B}{h:B->A}{e1:∀ i, h (f i) = i}: Function.Bijective (fun i => h (f i)) := by
  refine Function.Involutive.bijective ?_
  unfold Function.Involutive
  intro a
  dsimp
  rewrite [e1, e1]
  rfl

-- example {f:A->B}{h:B->A}{p1: f a = f b -> a = b}{k:f a = f b}: ∀ i, f (h i) = i := by
--   intro i
--   let _ := p1 k

-- example {A:Type}{A:Type}{f:A->B}{h:B->A}{e1:∀ i, h (f i) = i}
--   {p1:Function.Bijective (fun i => h (f i))}: ∀ i, f (h i) = i
-- := by
--   let ⟨ l , r ⟩ := p1
--   unfold Function.Injective at l
--   unfold Function.Surjective at r


--   admit

-- example : Function.Surjective h = Function.LeftInverse h f := by
--   unfold Function.LeftInverse Function.Surjective
--   apply propext
--   apply Iff.intro
--   {
--     intro i k
--     let ⟨ _ , p ⟩ := i k
--     rw [<-p]

--     admit
--   }
--   {
--     intro k i
--     refine ⟨ f i , ?_ ⟩
--     exact (k i)
--   }

def nat2list : Nat -> List Unit
| .zero => .nil
| .succ a => .cons () (nat2list a)
def list2nat : List Unit -> Nat
| .nil => .zero
| .cons .unit t => .succ (list2nat t)

def ln_coh : (a : List Unit) -> nat2list (list2nat a) = a := by
  intro i
  match i with
  | .cons () a => unfold list2nat nat2list; simp; exact (ln_coh a)
  | .nil => unfold list2nat nat2list; simp;

def list_int : wmap (List Unit) Nat := mkwmap list2nat nat2list ln_coh


def fmap_append_plus :
    (nat2list a1) ++ (nat2list a2) = nat2list (a1 + a2)
:= by
  cases a1
  {
    cases a2 <;> unfold nat2list <;> simp
  }
  {
    cases a2
    {
      case _ a =>
        unfold nat2list
        simp
    }
    {
      case _ a b =>
        rw [Nat.add_add_add_comm]
        unfold nat2list
        simp
        induction a
        {
          simp [nat2list]
        }
        {
          case _ n ih =>
            simp [nat2list]
            rw [ih]
            rw [Nat.add_right_comm _ 1 b]
        }
    }
  }


example : (a:List Unit) ++ b = b ++ a := by
  let (.mk a1 r1) := transp list_int a
  let (.mk a2 r2) := transp list_int b
  rw [<-r1, <-r2]
  unfold list_int mkwmap
  simp
  repeat rw [fmap_append_plus]
  apply congrArg
  rw [Nat.add_comm]


def invertible (f:A->B) := { h:B->A // ∀ i, h (f i) = i }

def symm_fun_inj: (p1: invertible f) -> Function.Injective f := by
  intro ⟨ h , p ⟩
  exact Function.LeftInverse.injective p

def symm_fun_inj_2: (p1: invertible f) -> (f a = f b) = (a = b) := by
  intro ⟨ h , p ⟩
  apply propext
  apply Iff.intro
  let x : Function.Injective f := by
    exact Function.LeftInverse.injective p
  intro k
  exact x k
  intro i
  exact congrArg f i

def strict : Bool -> Type | .true => Unit | .false => Empty


def homom_1 (h:A->B) (op1:A->A) (op2:B->B) := ∀ i, op2 (h i) = h (op1 i)
def homom_2 (h:A->B) (op1:A->A->A) (op2:B->B->B) := ∀ a b, h (op1 a b) = op2 (h a) (h b)

def homom_2_exists {A:Sort _}{B:Sort _}{op:A->A->A}:
  (w:wmap A B) -> let (.mk (.mk f h) _) := w;
  @Subtype (B->B->B) fun opm => (homom_2 h opm op) ∧
                                (opm = fun (b1:B) (b2:B) => f (op (h b1) (h b2)))
:= by
  intro w
  let (.mk (.mk f h) p1) := w
  simp
  refine ⟨?val, ?property⟩
  exact fun b1 b2 =>
    f (op (h b1) (h b2))
  simp at p1
  unfold homom_2
  dsimp
  apply And.intro
  intro a b
  rewrite [(p1 (op (h a) (h b)))]
  rfl
  rfl

def fmap_shl {A:Sort _}{B:Sort _}{op:A->A->A}{opm:B->B->B}{a b:B}:
  (w:wmap A B) -> let (.mk (.mk f h) _) := w;
  (f (op (h a) (h b)) = (opm a b)) ->
  (op (h a) (h b) = h (opm a b))
:= by
  intro ⟨ (.mk f h), p ⟩
  simp at p; simp
  intro i
  rw [<-i, p]

example :
  homom_2 nat2list (Nat.add) (List.append)
:= by
  unfold homom_2
  intro a1 a2
  rw [@List.append_eq]
  rw [@Nat.add_eq]
  cases a1
  {
    cases a2 <;> unfold nat2list <;> simp
  }
  {
    cases a2
    {
      case _ a =>
        unfold nat2list
        simp
    }
    {
      case _ a b =>
        rw [Nat.add_add_add_comm]
        unfold nat2list
        simp
        induction a
        {
          simp [nat2list]
        }
        {
          case _ n ih =>
            simp [nat2list]
            rw [<-ih]
            rw [Nat.add_right_comm _ 1 b]
        }
    }
  }


def wmap_symm (w:wmap A B)(eq1:Function.Surjective w.val.fst): wmap B A := by
  let (.mk (.mk f h) p) := w
  dsimp at p
  refine mkwmap h f ?_
  dsimp at eq1
  unfold Function.Surjective at eq1
  intro b
  let (.intro a r) := eq1 b
  rw [<-r]
  rw [p]

def inv_to_surjective {f:A->B}{h:B->A}(eq:∀ i, f (h i) = i) : Function.Surjective f := by
  exact Function.RightInverse.surjective eq



def fiber (b:B)(f: A->B) := { a // f a = b }
def is_contr (T:Sort _) := { i:T // ∀ t:T, i = t }
def is_equiv (f:A->B) := ∀ b:B, is_contr (fiber b f)
def weq (A:Sort _)(B:Sort _) := (f:A->B) ×' is_equiv f

def wmap_to_quot (w:wmap A B) : wmap A (@Quot B (fun a b => w.val.snd a = w.val.snd b)) := by
  let (.mk (.mk f h) p) := w
  reduce at p
  refine Subtype.mk (.mk ?_ ?_) ?_
  {
    intro i
    reduce
    refine Quot.mk _ ?_
    exact f i
  }
  {
    dsimp
    intro i
    refine Quot.lift ?_ ?_ i
    exact h
    intro _ _ h
    exact h
  }
  {
    reduce
    intro _
    rewrite [p]
    rfl
  }

set_option pp.proofs true in
def wmap_to_quot_inv (w:wmap A B) : wmap (@Quot B (fun a b => w.val.snd a = w.val.snd b)) A := by
  let (.mk (.mk f h) p1) := w
  dsimp at p1
  dsimp
  refine .mk (.mk ?_ ?_) ?_
  {
    intro i
    refine Quot.lift h ?_ i
    exact fun a b a => a
  }
  {
    intro a
    exact Quot.mk _ (f a)
  }
  {
    dsimp
    intro i
    let ⟨ _ , p ⟩  := Quot.exists_rep i
    rewrite [<-p]
    apply Quot.sound
    rewrite [p1]
    rfl
  }





def wmap_level_n (n:Nat)(A B) := match n with
  | .zero => wmap A B
  | .succ a => wmap (wmap_level_n a A B) (wmap_level_n a A B)

example : is_contr (wmap_level_n 0 Unit Unit) := by
  unfold is_contr
  refine (.mk ?_ ?_)
  refine (.mk (.mk id id) ?_)
  reduce
  intro
  rfl
  intro
  rfl

def contr_to_contr_fun_sp: is_contr T -> is_contr (T -> T) := by
  intro (.mk cc p)
  refine .mk id ?_
  intro f
  funext i
  generalize f i = k
  rewrite [<- p i, <- p k, id_def]
  rfl


-- set_option pp.proofs true in
-- example : is_contr (wmap A A) := by
--   refine (.mk (.mk (.mk ?_ ?_) ?_) ?_)
--   exact id
--   exact id
--   dsimp
--   intro
--   rfl
--   intro (.mk (.mk f h) p)
--   reduce at p
--   congr

-- set_option pp.proofs true in
-- example : is_contr (wmap_level_n 1 Bool Bool) := by
--   unfold is_contr
--   refine (.mk ?_ ?_)
--   refine (.mk (.mk id id) ?_)
--   reduce
--   intro
--   rfl
--   intro (.mk (.mk f h) p)
--   simp only [wmap_level_n] at f h
--   reduce at p
--   simp only [wmap_level_n] at p
--   rw [id_def (congrFun rfl)]

-- set_option pp.proofs true in
-- example : is_contr (wmap_level_n 2 Bool Bool) := by
--   unfold is_contr
--   refine (.mk ?_ ?_)
--   refine (.mk (.mk ?_ ?_) ?_)
--   {

--   }
--   {

--   }
--   reduce
--   intro
--   rfl
--   intro (.mk (.mk f h) p)
--   simp only [wmap_level_n] at f h
--   reduce at p
--   simp only [wmap_level_n] at p
--   rw [id_def (congrFun rfl)]



set_option pp.proofs true in
def transp_eqn_1 : (transp (wmap_to_quot_inv m1) (transp (wmap_to_quot m1) k)).val = k := by
  generalize (transp (wmap_to_quot m1) k) = j1
  simp at j1
  let (.mk v1 p) := j1
  dsimp
  rw [<-p]
  rfl

-- #check (transp (wmap_to_quot list_int) [])
-- #check (transp (wmap_to_quot_inv list_int) (transp (wmap_to_quot list_int) []))

-- example : (a:List Unit) ++ b = b ++ a := by
--   let (.mk v1 p1) := (transp (wmap_to_quot list_int) a)
--   let (.mk v2 p2) := (transp (wmap_to_quot list_int) b)
--   dsimp at p1 p2
--   rw [<-p1,<-p2]


def int_mod_2_bool : wmap Bool Nat := by
  refine mkwmap ?_ ?_ ?_
  intro b
  cases b
  exact 0
  exact 1
  intro n
  match n with | .zero => exact .false | .succ _ => exact .true
  intro b
  cases b
  dsimp
  dsimp

-- example {b:Bool} : Unit := by
--   let k := wmap_to_quot int_mod_2_bool
--   let k2 := transp k
