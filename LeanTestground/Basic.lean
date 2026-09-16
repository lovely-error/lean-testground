import Mathlib.Logic.Basic
import Mathlib.Logic.Function.Basic
import Mathlib.Tactic
import Mathlib.Logic.Equiv.Basic

macro "rwi" pat:term "=>" new:term ":=" prf:term : tactic =>
  `(tactic| rewrite [let _eq : $pat = $new := $prf ; _eq ])

macro "rwi" pat:term "=>" new:term "at" loc:Lean.Parser.Tactic.locationHyp ":=" prf:term : tactic =>
  `(tactic| rewrite [let _eq : $pat = $new := $prf ; _eq ] at $loc)


def wmap (A:Sort _)(B:Sort _) :=
  (p: (A -> B) ×' (B -> A)) ×' ∀ i, p.2 (p.1 i) = i

def fiber (f:A->B)(b:B) := (a:A) ×' f a = b

def wtransp : (w:wmap A B) -> ∀ a:A , fiber w.1.2 a :=
  fun w a => .mk (w.1.1 a) (w.2 _)


@[reducible]
def SubstRule1 {A:Sort _1}{B:Sort _2} (h:B->A) :=
  ∀ (a:A), (b:B) ×' (∀ (P:A->Sort _), P (h b) -> P a)

def wsubst (w:wmap A B): SubstRule1 w.1.2 := by
  unfold SubstRule1
  intro a
  refine .mk ?_ ?_
  exact (wtransp w a).1
  intro P
  unfold wtransp
  rw [w.2]
  intro i
  exact i

@[simp]
def wsubst_eqn_1 (w:wmap A B) : (wsubst w i).1 = w.1.1 i := rfl
grind_pattern wsubst_eqn_1 => (wsubst w i).1

def mkwmap (f: A->B)(h:B->A)(p: ∀ i, h (f i) = i) : wmap A B := ⟨ ⟨ f , h ⟩  , p ⟩

def id_wmap : wmap T T := by
  refine mkwmap id id ?_
  intro i
  rfl

@[simp]
def mkwmap_eqn_1 : mkwmap f h p = .mk (.mk f h) p := rfl
grind_pattern mkwmap_eqn_1 => mkwmap f h p

def hmor1 (op1:B->B)(op2:A->A)(p:A->B) :=
  ∀ a1, op1 (p a1) = p (op2 a1)

def hmor2 (op1:B->B->B)(op2:A->A->A)(p:A->B) :=
  ∀ a1 a2, op1 (p a1) (p a2) = p (op2 a1 a2)

def hmor2_exists {A:Sort _}{B:Sort _}(w:wmap A B) (op:A->A->A):
  let (.mk (.mk f h) _) := w;
  @Subtype (B->B->B) fun opm => (hmor2 op opm h) ∧
                                (opm = fun (b1:B) (b2:B) => f (op (h b1) (h b2)))
:= by
  let (.mk (.mk f h) p1) := w
  simp
  refine .mk ?val ?property
  exact fun b1 b2 =>
    f (op (h b1) (h b2))
  simp at p1
  unfold hmor2
  dsimp
  apply And.intro
  intro a b
  rewrite [(p1 (op (h a) (h b)))]
  rfl
  rfl

set_option pp.proofs true in
@[grind .]
theorem shift_tr_fun {a:A}{b:B}(w:wmap A B)(h1:w.1.1 a = b): w.1.2 b = a := by
  let (.mk (.mk f h) p1) := w
  dsimp at p1 h1
  dsimp
  rw [<-h1]
  rw [p1]

@[simp]
def shift_tr_fun_g {f:A->B}{h:B->A}{a:A}{b:B}(c:∀ i, h (f i) = i)(h1:f a = b): h b = a := by
  rw [<-h1, c]

set_option bootstrap.inductiveCheckResultingUniverse false in
inductive PProp.{u} (A:Prop): (Sort u)
  | intro (v:A)

def pprop_irrel (a b:PProp K): a = b := by
  cases a
  cases b
  congr

def path {A:Sort _} (a b:A) := ∀ (P:A->Sort _), P a -> P b

def path_trans (p1:path a b)(p2:path b c): path a c :=
  fun P pa => p2 P (p1 P pa)

def path_inv {A:Sort _} {a b:A} (p:path a b): path b a :=
  fun P => p (fun x => P x -> P a) id

def id_path (i:A): path i i := fun _ => id

def map_on_paths {f:A->B} (p:path a b): path (f a) (f b) :=
  fun P => p (fun i => P (f i))

def path_subst {A : Sort _} {a b : A} (P : A -> Sort _) (p : path a b) (x : P a) : P b :=
  p P x


def eq_is_path_prop {T:Sort _}{a b:T}: (a = b) = (path a b) := by
  apply propext
  apply Iff.intro
  {
    intro i
    cases i
    intro _
    apply id
  }
  {
    intro k
    let eq := k (fun i => a = i) rfl
    exact eq
  }

def eq_to_path (eq:a = b): path a b := by
  intro P pa
  cases eq
  exact pa

def path_to_eq {A:Sort _u} {a b:A}(p:path a b): a = b := by
  let (.intro k) := p (fun i => PProp (a = i)) (.intro (.refl a))
  cases k
  rfl


def eq_is_path {A:Sort u1}(a b:A) : wmap (a = b) (path.{_, u1} a b) := by
  refine mkwmap ?_ ?_ ?_
  {
    intro v
    exact eq_to_path v
  }
  {
    intro k
    let x := path_to_eq k
    exact x
  }
  {
    intro i
    dsimp
  }

#print axioms eq_is_path

axiom parametricity (f: (T:Sort _) -> T -> T): f = fun _ => id

def Parm.{u1,u2} := ∀ (T:Sort u1)(i:T)(p:path.{u1,u2} i i), p = id_path i

def path_is_eq (pm:Parm) {A:Sort u1}(a b:A) : wmap (path.{_, u1} a b) (a = b) := by
  refine mkwmap ?_ ?_ ?_
  {
    intro k
    let x := path_to_eq k
    exact x
  }
  {
    intro (v)
    exact eq_to_path v
  }
  {
    intro i
    dsimp
    generalize (PProp.intro.{u1} (path_to_eq i)).1 = j
    cases j
    unfold eq_to_path
    dsimp
    symm
    apply pm
  }

-- set_option pp.proofs true in
-- def path_is_eq_p {A:Sort _}(a b:A) : wmap (path a b) (PProp (a = b)) := by
--   refine mkwmap ?_ ?_ ?_
--   {
--     intro p
--     let x := path_to_eq p
--     exact .intro x
--   }
--   {
--     intro (.intro p)
--     exact eq_to_path p
--   }
--   {
--     intro p
--     dsimp
--     funext P i
--     generalize path_to_eq p = j1
--     unfold eq_to_path
--     cases j1
--     dsimp
--     admit
--   }

def invertible {A B:Sort _}(f:A->B) := { h:B->A // ∀ i, h (f i) = i }

def invertible_to_wmap {f:A->B} : (invertible f) -> (wmap A B) := by
  intro (.mk h eq1)
  exact mkwmap f h eq1
def wmap_to_invertible : (w:wmap A B) -> (invertible w.1.1) := by
  intro (.mk (.mk f h) eq1)
  exact .mk h eq1

def invertible_is_wmap {f:A->B}: wmap (invertible f) ({ w:wmap A B // w.1.1 = f }) := by
  refine mkwmap ?_ ?_ ?_
  {
    intro i
    refine .mk (invertible_to_wmap i) ?_
    let (.mk _ _) := i
    unfold invertible_to_wmap mkwmap
    dsimp
  }
  {
    intro (.mk w p)
    subst p
    exact wmap_to_invertible w
  }
  intro _
  rfl

def wmap_left_injective (w:wmap A B) : Function.Injective w.1.1 := by
  let (.mk (.mk f h) eq) := w
  exact Function.LeftInverse.injective eq

def invertible_to_injective (w:invertible f): Function.Injective f := by
  intro a b p
  let (.mk k p2) := w
  rw [<- p2 a, <- p2 b]
  congr

def invertible_to_injective_2 (w:invertible f): f a = f b -> a = b := by
  intro h
  let x := invertible_to_wmap w
  let k := wmap_left_injective x
  exact k h

@[reducible]
def wmap_fiber_thining_rel (w:wmap A B)(b1 b2: B) := w.1.2 b1 = w.1.2 b2

def wmap_to_quot (w:wmap A B) : wmap A (@Quot B (wmap_fiber_thining_rel w)) := by
  refine mkwmap ?_ ?_ ?_
  {
    intro i
    exact Quot.mk _ (w.1.1 i)
  }
  {
    intro i
    refine Quot.lift w.1.2 (fun _ _ => id) i
  }
  {
    intro _
    dsimp
    rw [w.2]
  }


set_option pp.proofs true in
def wmap_to_quot_inv (w:wmap A B) : wmap (@Quot B (wmap_fiber_thining_rel w)) A := by
  refine .mk (.mk ?_ ?_) ?_
  {
    intro i
    refine Quot.lift w.1.2 (fun _ _ => id) i
  }
  {
    intro a
    exact Quot.mk _ (w.1.1 a)
  }
  {
    dsimp
    intro i
    let ⟨ _ , p ⟩ := Quot.exists_rep i
    rewrite [<-p]
    apply Quot.sound
    unfold wmap_fiber_thining_rel
    rewrite [w.2]
    rfl
  }

@[simp]
def quot_transp_eqn_2 : (wtransp (wmap_to_quot_inv m1) (wtransp (wmap_to_quot m1) k).1).1 = k := by
  let (.mk j1 p) := wtransp id_wmap (wtransp (wmap_to_quot m1) k)
  rw [<-p]
  simp [id_wmap]
  let (.mk v1 p) := j1
  simp
  rw [<-p]
  rfl
grind_pattern quot_transp_eqn_2 => (wtransp (wmap_to_quot_inv m1) (wtransp (wmap_to_quot m1) k).1).1

-- every equivalence class contains one canonical element
def wmap_eqvc_can_el_eqn (w:wmap A B):
  (@Quot.mk B (wmap_fiber_thining_rel w) (i))
    =
  (@Quot.mk B (wmap_fiber_thining_rel w) (w.1.1 (w.1.2 i)))
:= by
  refine Quot.sound ?_
  unfold wmap_fiber_thining_rel
  rw [w.2 _]


def hmor_shl {A:Sort _}{B:Sort _}(opa:A->A->A)(opb:B->B->B)(w:wmap A B){v1 v2}:
  ((opb v1 v2) = w.1.1 (opa (w.1.2 v1) (w.1.2 v2))) ->
  (w.1.2 (opb v1 v2) = opa (w.1.2 v1) (w.1.2 v2))
:= by
  let ⟨ (.mk f h), p ⟩ := w
  dsimp at p; dsimp
  intro i
  rw [i, p]


def wmap_trans (w1:wmap A B)(w2: wmap B C): wmap A C := by
  let (.mk (.mk f1 f2) p1) := w1
  dsimp at p1
  let (.mk (.mk f3 f4) p2) := w2
  dsimp at p2
  refine mkwmap ?_ ?_ ?_
  {
    intro a
    exact f3 $ f1 a
  }
  {
    intro c
    exact f2 $ f4 c
  }
  {
    intro i
    rw [p2, p1]
  }


def fun2 (w:wmap A (@Quot B r)): B -> A := by
  intro i
  let x := wmap_to_quot_inv w
  let k := wtransp x (Quot.mk _ (Quot.mk _ i))
  reduce at k
  exact k.1

def fun3 {h:B->A}(k:invertible h)(w:wmap A (@Quot B (fun a b => h a = h b))): A -> B := by
  intro i
  let (.mk v p2) := wtransp w i
  refine Quot.recOn v ?_ ?_
  apply id
  intro a b p
  simp only [id_eq, eq_rec_constant]
  let x := invertible_to_injective_2 k p
  exact x



def SEq A B := (w:wmap A B) ×' SubstRule1 w.1.2

def half_uv {A B:Sort i}: wmap (wmap A B) (SEq.{_, i} A B) := by
  refine mkwmap ?_ ?_ ?_
  {
    intro w
    refine .mk ?_ ?_
    exact w
    intro k
    exact wsubst w k
  }
  {
    intro s
    unfold SEq at s
    let (.mk r m) := s
    exact r
  }
  {
    intro i
    dsimp
  }

#print axioms half_uv

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

-- def nl_coh : (a : Nat) -> list2nat (nat2list a) = a := by
--   intro i
--   match i with
--   | .succ a => unfold list2nat nat2list; simp; exact (nl_coh a)
--   | .zero => unfold list2nat nat2list; simp;

def list_nat : wmap (List Unit) Nat := mkwmap list2nat nat2list ln_coh

-- def hmor_append_plus : hmor2 (List.append) (Nat.add) (nat2list) := by
--   intro a1 a2
--   dsimp only [List.append_eq, Nat.add_eq]
--   cases a1
--   {
--     simp_all only [Nat.zero_eq, zero_add, shift_tr_fun_g, List.append_left_eq_self]
--     rfl
--   }
--   {
--     cases a2
--     {
--       simp_all only [Nat.succ_eq_add_one, Nat.zero_eq, add_zero, List.append_right_eq_self]
--       rfl
--     }
--     {
--       case _ a b =>
--         dsimp only [Nat.succ_eq_add_one]
--         rw [Nat.add_add_add_comm]
--         unfold nat2list
--         simp only [List.cons_append, List.cons.injEq, true_and]
--         induction a
--         {
--           simp [nat2list]
--         }
--         {
--           case _ n ih =>
--             simp [nat2list]
--             rw [ih]
--             rw [Nat.add_right_comm _ 1 b]
--         }
--     }
--   }

-- def hmor_append_plus : hmor2 (List.append) Nat.add nat2list := by
--   intro a b
--   symm
--   fun_induction nat2list (a)
--   {
--     simp only [Nat.zero_eq, Nat.add_eq, zero_add, List.append_eq, List.nil_append]
--   }
--   {
--     case _ a ih =>
--     simp_all only [Nat.add_eq, List.append_eq, Nat.succ_eq_add_one, List.cons_append]
--     rw [<-ih]
--     rw [Nat.add_right_comm, Nat.add_one]
--     conv =>
--       arg 1
--       unfold nat2list
--   }

def hmor_append_plus : hmor2 (List.append) Nat.add nat2list := by
  intro a b
  fun_induction nat2list a
  {
    aesop
  }
  case _ _ ih =>
  simp_all only [List.append_eq, Nat.add_eq, List.cons_append, Nat.succ_eq_add_one]
  rw [<-ih]
  rw [Nat.add_right_comm, Nat.add_one]
  conv =>
    arg 2; reduce
  congr


example {p q:List Unit} : (p ++ q) = (q ++ p) := by
  let x := wtransp half_uv list_nat
  -- unfold list_nat half_uv at x
  let (.mk (.mk _ x2) s1) := x
  subst s1
  let (.mk p r1) := x2 p
  apply r1
  let (.mk q r2) := x2 q
  apply r2

  let h := hmor_append_plus
  unfold hmor2 at h
  dsimp at h
  reduce; dsimp
  repeat rw [h]
  apply congrArg

  apply Nat.add_comm p q


def is_center (v:T) := ∀ (i:T), i = v
def is_contr (T:Sort _) := (cc:T) ×' is_center cc
def is_equiv (f:A->B) := ∀ i, is_contr (fiber f i)
def weq (A B) := (f:A->B) ×' is_equiv f

def weq_to_inv_fun (w:weq A B): B -> A := by
  intro b
  exact (w.2 b).1.1

@[simp]
def weq_to_inv_eqn_1 (w:weq A B) : weq_to_inv_fun w = fun i => (w.2 i).1.1 := rfl
grind_pattern weq_to_inv_eqn_1 => weq_to_inv_fun w

@[simp]
def weq_cancel_eqn_1 (w:weq A B) : w.fst (weq_to_inv_fun w i) = i := by
  let (.mk f cf) := w
  simp only [weq_to_inv_eqn_1]
  let (.mk k p) := wtransp id_wmap (cf i)
  simp [id_wmap] at p
  rw [<-p]
  let (.mk (.mk v eq1) _) := k
  dsimp
  exact eq1
grind_pattern weq_cancel_eqn_1 => w.fst (weq_to_inv_fun w i)

def weq_subst (w:weq A B): SubstRule1 w.1 := by
  intro b
  refine .mk ?_ ?_
  {
    exact (weq_to_inv_fun w) b
  }
  {
    intro P
    rw [weq_cancel_eqn_1]
    apply id
  }

def id_weq : weq T T := by
  refine .mk id ?_
  intro i
  refine .mk ?_ ?_
  refine .mk i ?_
  rfl
  intro k
  let (.mk _ p) := k
  subst p
  rfl

def id_subst_rule : SubstRule1 (@id T) := by
  intro i
  refine .mk i ?_
  intro P
  apply id

def iso A B := @Subtype ((A->B) ×' (B->A)) fun (.mk f h) => (∀ i, f (h i) = i) ∧ (∀ i, h (f i) = i)

def mkiso (f:A->B)(h:B->A)(c1:∀ i, f (h i) = i)(c2:∀ i, h (f i) = i): iso A B := .mk (.mk f h) (.intro c1 c2)

@[simp]
def mkiso_eqn_1 : mkiso f h p1 p2 = .mk (.mk f h) (.intro p1 p2) := rfl
grind_pattern mkiso_eqn_1 => mkiso f h p1 p2

def subtype_ext_rev {p:A->Prop}{a b:Subtype p} : (a = b) -> (a.val = b.val) := by
  exact fun a_1 => congrArg Subtype.val a_1

def psig_ext_rev {p:A->Prop}{a b:PSigma p} : (a = b) -> (a.1 = b.1) := by
  intro eq
  cases eq
  rfl

def weq_is_iso : wmap (weq A B) (iso A B) := by
  refine mkwmap ?_ ?_ ?_
  {
    intro w
    refine .mk (.mk ?_ ?_) (.intro ?_ ?_)
    exact w.fst
    {
      intro b
      let (.mk (.mk a _) _) := w.snd b
      exact a
    }
    intro b
    let (.mk j1 k) := wtransp id_wmap (w.snd b)
    rw [<-k]
    let (.mk (.mk _ p) _) := j1
    exact p
    {
      intro a
      let (.mk j1 k) := wtransp id_wmap (w.snd (w.fst a))
      rw [<-k]
      let (.mk (.mk v p) z) := j1
      reduce
      let fa : fiber w.fst (w.fst a) := by
        refine .mk a ?_
        rfl
      let x := z fa
      unfold fa at x
      let k := psig_ext_rev x
      simp at k
      symm
      exact k
    }
  }
  {
    intro w
    refine .mk w.1.1 ?_
    intro b
    let cf : fiber w.1.1 b := by
      refine .mk (w.1.2 b) ?_
      exact w.property.left _
    refine .mk cf ?_
    intro (.mk v p)
    unfold cf
    subst p
    let x := w.property.right v
    congr
    symm
    exact x
  }
  {
    intro i
    exact rfl
  }

def iso_to_equiv (i:iso A B): Equiv A B := by
  refine { toFun := i.1.1, invFun := i.1.2, left_inv:=?_, right_inv:=?_ }
  refine Function.leftInverse_iff_comp.mpr ?_
  let x := i.2.2
  reduce at x
  exact Function.RightInverse.id x
  let x := i.2.1
  reduce at x
  exact Function.LeftInverse.rightInverse x

def weq_transp (w:weq A B): ∀ i, fiber (weq_to_inv_fun w) i := by
  intro i
  refine .mk (w.fst i) ?_
  unfold weq_to_inv_fun
  let (.mk (.mk (.mk f h) (.intro _ r)) p) := wtransp weq_is_iso w
  rw [<-p]
  unfold weq_is_iso mkwmap
  simp
  apply r


def weq_inv_is_weq (w:weq A B): is_equiv (weq_to_inv_fun w) := by
  intro i
  refine .mk ?_ ?_
  {
    exact weq_transp w i
  }
  {
    intro p
    unfold weq_transp
    let (.mk v k) := p
    subst k
    unfold weq_to_inv_fun
    let (.mk f q) := w
    simp
    unfold is_equiv at q
    congr
    let (.mk (.mk _ j) _) := q v
    simp
    rw [j]
  }

def weq_inverse (w:weq A B): weq B A := by
  refine .mk ?_ ?_
  exact weq_to_inv_fun w
  exact weq_inv_is_weq w

def weq_to_wmap (w:weq A B): wmap B A := by
  let (.mk f eq) := w
  refine mkwmap ?_ ?_ ?_
  {
    intro b
    let (.mk (.mk a _) _) := eq b
    exact a
  }
  exact f
  {
    intro i
    let (.mk (.mk _ p) _) := eq i
    simp
    rw [p]
  }

def quot_map_is_equiv (w:wmap A B) : is_equiv (wmap_to_quot_inv w).1.1 := by
  unfold is_equiv
  intro i
  refine .mk ?_ ?_
  {
    refine .mk ?_ ?_
    exact Quot.mk _ (w.1.1 i)
    simp [wmap_to_quot_inv]
    rw [w.2]
  }
  intro k
  let (.mk q p) := k
  congr
  let (.intro _ x) := Quot.exists_rep q
  rw [<-p, <-x]
  simp [wmap_to_quot_inv]
  exact wmap_eqvc_can_el_eqn w

def wmap_to_weq_on_quot (w:wmap A B): weq (@Quot B (wmap_fiber_thining_rel w)) A := by
  refine .mk ?_ ?_
  let x := wmap_to_quot_inv w
  exact x.1.1
  exact quot_map_is_equiv w

def rule1
  (w:wmap A B)
  (h2:invertible w.1.2)
: is_contr (fiber (fun b => w.1.2 b) a)
:= by

  let p := quot_map_is_equiv w
  let x1 := p a
  let (.mk cc p1) := x1
  let (.mk cc2 p2) := cc
  let x := Quot.mk (wmap_fiber_thining_rel w) (w.1.1 a)
  refine .mk ?_ ?_
  {
    refine .mk ?_ ?_
    exact (wtransp w a).1
    reduce
    exact shift_tr_fun w rfl
  }
  intro i
  let (.mk h p) := i
  dsimp at p
  congr
  rw [<-p]
  reduce
  let x := invertible_to_injective_2 h2 (a:=h) (b:=w.1.1 (w.1.2 h))
  apply x
  rw [w.2]


def rule1_2
  (f:A->B)
  (h:B->A)
  (p:∀ i, h (f i) = i)
  (h2:invertible h)
: is_contr (fiber (fun b => h b) a)
:= by
  let w := mkwmap f h p
  exact rule1 w h2

def wmap_to_weq (w1:wmap A B)(h1:invertible w1.1.2) : weq B A := by
  refine .mk ?_ ?_
  {
    intro b
    let (.mk v _) := wtransp (wmap_to_quot_inv w1) (Quot.mk _ b)
    exact v
  }
  {
    intro a
    exact rule1 w1 h1
  }

def wmap_to_weq_2 (w1:wmap A B)(w2:wmap B A)(c1: w1.1.2 = w2.1.1) : weq B A := by
  let x := wmap_to_invertible w2
  refine wmap_to_weq w1 ?_
  refine .mk x.1 ?_
  intro i
  reduce
  exact shift_tr_fun w2 (congrFun (Eq.symm c1) i)


def wmap_invert (w1:wmap A B)(h1:invertible w1.1.2) : wmap B A := by
  refine mkwmap ?_ ?_ ?_
  { exact w1.1.2 }
  { exact h1.1 }
  intro i
  let (.mk a b) := h1
  exact b i

def wmap_loop (w1:wmap A B)(w2:wmap B A)(c1: w1.1.2 = w2.1.1) : w1.1.1 = w2.1.2 := by
  cases w1
  cases w2
  case _ a b c d =>
  cases a
  cases c
  case _ f1 f2 f3 f4 =>
  simp at b d c1
  dsimp only
  subst c1
  funext i
  let x := d (f1 i)
  rw [<-x]
  congr
  rw [b]

def wmap_to_iso (w1:wmap A B)(w2:wmap B A)(c1: w1.1.2 = w2.1.1): iso A B := by
  refine mkiso ?_ ?_ ?_ ?_
  { exact w2.1.2 }
  { exact w1.1.2 }
  {
    intro i
    rw [c1]
    exact shift_tr_fun w2 rfl
  }
  {
    intro i
    let x := wmap_loop w1 w2 c1
    rw [<-x]
    exact shift_tr_fun w1 rfl
  }

def iso_is_weq : wmap (iso A B) (weq A B) := by
  refine wmap_invert ?_ ?_
  { exact weq_is_iso }
  {
    refine .mk ?_ ?_
    intro i
    refine mkiso ?_ ?_ ?_ ?_
    exact i.1
    { exact (weq_inverse i).1 }
    {
      intro v
      apply weq_cancel_eqn_1
    }
    {
      intro v
      let (.mk f cf) := i
      unfold weq_inverse
      reduce
      let (.mk fib cp) := cf (f v)
      dsimp
      let x := cp (.mk v (by rfl))
      rw [<-x]
    }
    {
      intro i
      reduce
      let (.mk (.mk _ _) _) := i
      dsimp
    }
  }

def wmap_left_triangle_filler
  {A B C : Sort _}
  (w_gf : wmap A C)
  (w_g : wmap B C)
  (f : A -> B)
  (h_comp : ∀ i, w_gf.1.1 i = w_g.1.1 (f i))
: wmap A B
:= by
  let h_f := fun i => w_gf.1.2 (w_g.1.1 i)
  refine mkwmap f h_f ?_
  intro a
  unfold h_f
  exact shift_tr_fun w_gf (h_comp a)

structure Functorial (F:Sort _ -> Sort _) where
  map : (A -> B) -> (F A -> F B)
  map_id : ∀ (x : F A), map (id : A -> A) x = x
  map_comp : ∀ (f : A -> B) (g : B -> C) (x : F A),
    map (fun i => g (f i)) x = (map g) (map f x)

def wmap_fun_map {A:Sort _}{B:Sort _}(fu : Functorial F)(w : wmap A B) : wmap (F A) (F B) := by
  let p := w.1
  let f := p.1
  let h := p.2
  refine mkwmap (fu.map f) (fu.map h) ?_
  intro x
  rw [<- fu.map_comp]
  let k : (fun i => h (f i)) = id := funext w.2
  rw [k]
  exact fu.map_id x

#print axioms wmap_fun_map

def wsubst2 (w:wmap A B)(fu:Functorial F): F A -> F B := (wmap_fun_map fu w).1.1
def wsubst4 (w:wmap A B)(fu:Functorial F): F B -> F A := (wmap_fun_map fu w).1.2


def option_fu : Functorial Option := by
  refine {
    map := ?_
    map_id := ?_
    map_comp := ?_
  }
  exact Option.map
  intro _ x
  exact Option.map_id_apply
  intro _ _ _ f g p
  cases p
  simp only [Option.map_none]
  case _ val =>
  simp only [Option.map_some]

@[reducible]
def Example1 :=
  let x := wmap_fun_map option_fu list_nat
  let k := wtransp x (.some [])
  k.1 = .some 0

example : Example1 := by rfl

def iterf (n:Nat)(k:T->T): T -> T :=
  match n with
  | .zero => id
  | .succ a => fun i => k ((iterf a k) i)

def iterf_step_eqn : iterf (n + 1) f k = f (iterf (n) f k) := by
  rfl

def iterf_inner_acc_eqn : iterf (n + 1) f k = (iterf (n) f (f k)) := by
  induction  n
  rfl
  case _ n ih =>
  reduce; congr

def orbit (a:T)(k:T->T) := { i // iterf i k a = a }

def contr_ty_vals_irrel (c:is_contr T)(a b:T): a = b := by
  let e1 := c.2 a
  let e2 := c.2 b
  rw [e1, e2]

def contr_to_contr_fun_sp: is_contr T -> is_contr (T -> T) := by
  intro (.mk cc p)
  refine .mk id ?_
  intro f
  funext i
  let (.mk k p2) := wtransp id_wmap (f i)
  simp [id_wmap] at p2
  rw [<-p2]
  rewrite [p i, p k, id_def]
  rfl

def contr_sp_fun_irrel (c:is_contr T)(f h:T->T): f = h := by
  let x1 := contr_to_contr_fun_sp c
  let x2 := contr_ty_vals_irrel x1
  exact x2 f h

set_option pp.proofs true in
def contr_ty_to_contr_wmap : is_contr T -> is_contr (wmap T T) := by
  intro cpo
  let (.mk cc cp) := cpo
  refine .mk ?_ ?_
  exact id_wmap
  intro w
  let (.mk (.mk f h) p1) := w
  dsimp at p1
  let eq1 := contr_sp_fun_irrel cpo (f:=f) (h:=id)
  let eq2 := contr_sp_fun_irrel cpo (f:=h) (h:=id)
  congr


def contr_ty_to_id_wmap (c:is_contr T)(w:wmap T T): w = id_wmap := by
  let (.mk cc cp) := contr_ty_to_contr_wmap c
  rw [cp w, cp id_wmap]

set_option pp.proofs true in
def uvp (A B:Prop) : wmap (wmap A B) (A = B) := by
  refine mkwmap ?_ ?_ ?_
  {
    intro w
    refine Eq.propIntro ?_ ?_
    {
      intro i
      let b := wtransp w i
      exact b.1
    }
    {
      exact w.1.2
    }
  }
  {
    intro k
    cases k
    exact id_wmap
  }
  {
    intro i
    let (.mk (.mk _ _) _) := i
    congr
  }

#print axioms uvp

def eq_contr: is_contr (a = a) := by
  refine .mk ?_ ?_
  rfl
  intro i
  cases i
  rfl

def pprop_eq_contr (i:A) : is_contr (PProp (i = i)) := by
  refine .mk ?_ ?_
  exact .intro (.refl _)
  intro (.intro p)
  congr

@[simp]
def eq_centr_refl : (@eq_contr T i).1 = Eq.refl i := by
  rfl

def hmor_hf_to_fh (w1:wmap A B)(w2:wmap B A)(c1:w1.1.2 = w2.1.1)(h1:hmor1 h f w1.1.1): hmor1 f h w1.1.2 := by
  intro x
  let (.mk (.mk a b) p1) := w1
  let (.mk (.mk c d) p2) := w2
  unfold hmor1 at h1
  simp at p1 h1 p2 c1
  simp
  subst c1
  grind

-- def trivial_subst_on_id {T:Sort _} : is_contr (SubstRule1 (@id T)) := by
--   refine .mk ?_ ?_
--   {
--     intro i
--     refine .mk i ?_
--     intro P
--     apply id
--   }
--   {
--     intro k2
--     funext i
--     generalize k2 i = j
--     cases j
--     case _ v2 M =>
--     simp at M
--     let (.intro p) := M (fun i => PProp (i = v2)) (.intro (.refl _))
--     cases p
--     congr
--     funext K v

--     admit
--   }

structure WRules (A:Sort _1)(B:Sort _2) where
  eqv_fun: A -> B
  subst : SubstRule1.{_, _, max _1 _2} eqv_fun
  -- hmors1 : ∀ f:B->B, (h:A->A) ×' hmor1 f h eqv_fun
  hmors2 : ∀ f:B->B->B, (h:A->A->A) ×' hmor2 f h eqv_fun

def no_conf_hmor (w:WRules A B)(h)(f): (h = (w.hmors2 f).1) ∨ Not (h = (w.hmors2 f).1)  := by
  exact eq_or_ne h (w.hmors2 f).fst

def wmap_to_wrules (w:wmap A B): WRules B A := by
  refine { eqv_fun := ?_, subst := ?_, hmors2 := ?_ }
  exact w.1.2
  exact wsubst w
  {
    intro f
    refine .mk ?_ ?_
    let (.mk h p) := hmor2_exists w f
    exact h
    let (.mk j k) := wtransp id_wmap (hmor2_exists w f)
    simp [id_wmap] at k
    rw [<-k]
    let (.mk _ p) := j
    simp
    exact p.1
  }


-- example : hmor2 (List.append) Nat.add nat2list := by
--   unfold hmor2
--   simp
--   intro a b
--   let k := hmor_shl List.append Nat.add list_nat a b
--   unfold list_nat at k
--   simp at k
--   symm
--   apply k
--   let x := wmap_to_wrules list_nat
--   let k2 := no_conf_hmor x (Nat.add) (List.append)
--   unfold x wmap_to_wrules list_nat hmor2_exists at k2
--   simp at k2
--   cases k2
--   {
--     case _ p =>
--     rw [funext_iff] at p
--     let p := p a
--     rw [funext_iff] at p
--     let p := p b
--     simp at p
--     apply p
--   }
--   {
--     case _ n =>
--     eta_expand at n
--     simp at n
--     conv at n =>
--       arg 1
--       rw [funext_iff]
--       pattern _ = _
--       rw [funext_iff]
--     simp only [not_forall] at n

--     admit
--   }

def is_unit (T) := ∀ (a b:T), a = b

def is_equiv_contr (f:A->B) : is_unit (is_equiv f) := by
  unfold is_equiv
  intro a b
  funext i
  generalize a i = k1
  generalize b i = k2
  let (.mk fi1 p1) := k1
  let (.mk fi2 p2) := k2
  congr
  rw [<-p1 fi2]

inductive PreEq : A -> B -> Sort _ where
  | iden : PreEq i i
  | path (w: weq A B) : PreEq A B
  -- | glue1 : @PreEq2.path A A (@id_weq A) = @PreEq2.iden _ A

def pre_eq_eq_rel {a:A}{b:B}(x y: PreEq a b): Prop :=
  match x, y with
  | .iden, .iden => True
  | .path f, .path h => ∀ i, f.1 i = h.1 i
  | .path i, .iden => i = id_weq
  | .iden, .path i => i = id_weq


def Eq2 (a:A)(b:B) : Sort _ := @Quot (PreEq a b) pre_eq_eq_rel

def Eq2.iden {A : Sort _}{a:A} : Eq2 a a := Quot.mk _ PreEq.iden
def Eq2.path {A : Sort _}{B : Sort _} (w : weq A B) : Eq2 A B := Quot.mk _ (PreEq.path w)

def eq2_glue_1 : Eq2.path (@id_weq A) = Eq2.iden := by
  refine Quot.sound ?_
  unfold pre_eq_eq_rel
  rfl

def weq_to_eq2 (w:weq A B): Eq2 A B := by
  exact Eq2.path w

def eq2_to_weq (eq:Eq2 A B) : weq A B := by
  refine Quot.recOn eq ?_ ?_
  {
    intro eq
    cases eq
    {
      exact id_weq
    }
    {
      case _ w =>
      exact w
    }
  }
  {
    intro a b rel
    cases a
    {
      cases b
      {
        simp
      }
      {
        case _ w =>
        unfold pre_eq_eq_rel at rel
        simp at rel
        subst rel
        simp
      }
    }
    {
      cases b
      {
        case _ w =>
        unfold pre_eq_eq_rel at rel
        simp at rel
        subst rel
        simp
      }
      {
        case _ w1 w2 =>
        unfold pre_eq_eq_rel at rel
        simp at rel
        unfold weq at w1 w2
        let x : w1 = w2 := by
          let (.mk f p1) := w1
          let (.mk h p2) := w2
          simp at rel
          rw [<-funext_iff] at rel
          subst rel
          simp only [PSigma.mk.injEq, heq_eq_eq, true_and]
          let x := is_equiv_contr f p1 p2
          exact x
        dsimp
        rw [@eqRec_eq_cast]
        reduce
        exact x
      }
    }
  }

def eq2_is_weq : iso (Eq2 A B) (weq A B) := by
  refine mkiso eq2_to_weq weq_to_eq2 ?_ ?_
  {
    intro i
    cases i
    case _ f eqp =>
    unfold weq_to_eq2 eq2_to_weq
    rfl
  }
  {
    intro i
    refine Quot.recOn i ?_ ?_
    {
      intro k
      cases k
      {
        unfold weq_to_eq2 eq2_to_weq Eq2.path
        apply Quot.sound
        unfold pre_eq_eq_rel
        reduce
        rfl
      }
      {
        case _ w =>
        unfold weq_to_eq2 eq2_to_weq Eq2.path
        apply Quot.sound
        unfold pre_eq_eq_rel
        reduce
        intro _
        rfl
      }
    }
    {
      intro a b rel
      repeat rfl
    }
  }


-- https://github.com/ekiciburak/ua_funext/blob/master/UA_FE.v

def s442 (w:wmap A B): wmap (X -> A) (X -> B) := by
  refine mkwmap ?_ ?_ ?_
  {
    intro f x; exact wtransp w (f x) |>.1
  }
  {
    intro f x; exact w.1.2 (f x)
  }
  intro f
  unfold wtransp
  simp
  funext i
  rw [w.2]

def arrow_fu (T:Sort _): Functorial (fun K => T -> K) := by
  refine { map := ?_, map_id := ?_, map_comp := ?_ }
  {
    intro A B f h t
    exact f (h t)
  }
  {
    intro A B
    rfl
  }
  {
    intro A B C f h x
    reduce
    rfl
  }

def s442_2 (w:wmap A B): wmap (X -> A) (X -> B) := by
  let x := wmap_fun_map (arrow_fu X) w
  exact x

def s443 (P:A->Sort _)(p:∀ x:A, is_contr (P x)) : wmap (A -> (x:A) ×' P x) (A -> A) := by
  apply s442
  refine mkwmap ?_ ?_ ?_
  exact fun i => i.1
  {
    intro a
    refine .mk a ?_
    let x := p a
    exact x.1
  }
  intro x
  cases x
  dsimp
  congr
  case _ v p2 =>
  let (.mk j k) := wtransp id_wmap (p v)
  rw [<-k]
  let (.mk cc cp) := j
  rw [cp p2]
  reduce
  rfl

def h437_2 {A : Sort _}{B:Sort _} (re : wmap B A) (c : is_contr A) : is_contr B := by
  let (.mk (.mk r s) eps) := re
  let (.mk a p) := c
  refine .mk ?_ ?_
  exact s (a)
  intro y
  dsimp at eps
  rw [<-eps y]
  congr
  exact p (r y)

def wfunext {A : Sort _} {P : A → Sort _} : (∀ x:A, is_contr (P x)) → is_contr (∀ x:A, P x) := by
  intro k
  let x := s443 P k
  let map := x.1.1
  let h1 : invertible x.1.2 := .mk map (by intro; rfl)
  let x2 := wmap_to_iso x ((wtransp invertible_is_wmap h1).1.1) rfl
  let x3 := (wtransp iso_is_weq x2).1
  let cf := x3.2 id
  refine h437_2 ?_ cf
  refine mkwmap ?_ ?_ ?_
  {
    intro f
    refine .mk (fun x => .mk x (f x)) ?_
    reduce
    rfl
  }
  {
    intro (.mk sec q) v
    let x1 := (sec v).snd
    let x2 := congr_arg P (congr_fun q v)
    reduce at x2
    rw [<-x2]
    exact x1
  }
  {
    intro f
    reduce
    eta_reduce
    rfl
  }

#print axioms wfunext

def PointwiseEq {A : Sort u} {B : A -> Sort v} (f g : (x:A) -> B x) := ∀ x, f x = g x

def hap {A : Sort u} {B : A -> Sort v} {f g : (x:A) -> B x} (p : f = g) : PointwiseEq f g := by
  subst p
  intro x
  rfl

def sing_contr {A : Sort _} (a : A) : is_contr ((x : A) ×' a = x) := by
  refine .mk (.mk a rfl) ?_
  intro p
  let (.mk v eq) := p
  subst eq
  rfl

def total_hmtp_contr
  {A : Sort _}
  {B : A -> Sort _}
  (f : (x:A) -> B x)
: is_contr ((g : (x:A) -> B x) ×' PointwiseEq f g)
:= by
  -- 1. Define the fiber type for each x (Sigma type of value and equality)
  let P := fun x => (y : B x) ×' f x = y
  -- 2. Establish that fibers are contractible (using singleton_contr)
  let c : ∀ x, is_contr (P x) := fun x => sing_contr (f x)
  -- 3. Use wfunext to prove the Pi-type is contractible
  let (.mk center_pi contr_pi) := wfunext c
  refine .mk ?_ ?_
  {
    -- Center of the total space: (f, refl)
    refine .mk f ?_
    exact congrFun rfl
  }
  {
    intro (.mk g p)
    -- 4. Define the mapping from the Pi-type (∀ x, Σ y, ...) to the Sigma-type (Σ g, ∀ x, ...)
    -- This acts as a distributor
    let to_sig (k : ∀ x, P x) : ((g : (x:A) -> B x) ×' PointwiseEq f g) :=
      .mk (fun x => (k x).1) (fun x => (k x).2)
    -- 5. Construct the specific element in the Pi-type corresponding to (g, p)
    let el_pi : ∀ x, P x := fun x => .mk (g x) (p x)
    -- 6. Use the contraction from wfunext to find the path in the Pi-type
    -- This gives: (fun x => .mk (f x) rfl) = (fun x => .mk (g x) (p x))
    let path := contr_pi el_pi
    let dest := congrArg to_sig path
    let el_pi_2 : ∀ x, P x := fun x => .mk (f x) rfl
    let path2 := contr_pi el_pi_2
    let dest2 := congrArg to_sig path2
    rw [<-dest2] at dest
    reduce at dest
    congr
  }

#print axioms total_hmtp_contr

def fext
  {A : Sort _}
  {B : A -> Sort _}
  {f g : (x : A) -> B x}
  (h : ∀ x, f x = g x)
: f = g := by
  let total := total_hmtp_contr f
  let (.mk center contr) := total
  let T := (g : (x : A) -> B x) ×' PointwiseEq f g
  let l : T := .mk f (hap rfl)
  let r : T := .mk g h
  let path1 : l = center := contr l
  let path2 : r = center := contr r
  rw [<-path2] at path1
  let x := congrArg (fun i => i.1) path1
  reduce at x
  apply x

#print axioms fext


-- https://inria.hal.science/hal-01966714/document

def PreInt := Nat × Nat

def int_canon_repr (n:PreInt): PreInt :=
  let (.mk a b) := n
  match a, b with
  | .succ a, .succ b => int_canon_repr (.mk a b)
  | .zero, n => .mk .zero n
  | n, .zero => .mk n .zero
  termination_by n.fst + n.snd
  decreasing_by {
    omega
  }

def IntNFCst (n:PreInt) := n.1 = 0 ∨ n.2 = 0

def int_add (a b:PreInt): PreInt :=
  let (.mk a_1 b_1) := a
  let (.mk a_2 b_2) := b
  .mk (a_1 + a_2) (b_1 + b_2)

def negated (n:PreInt): PreInt := .mk (n.2) (n.1)

def repr_eqn_1 (k) : int_canon_repr (.mk a b) = int_canon_repr (.mk (a + k) (b + k)) := by
  cases k
  {
    rfl
  }
  {
    case _ k =>
    rw [Nat.add_succ]
    conv =>
      arg 2
      unfold int_canon_repr
    simp only [Nat.add_eq]
    apply repr_eqn_1
  }

def canon_repr_eqn_2 (i) : let v := int_canon_repr i; v.1 = 0 ∨ v.2 = 0 := by
  let (.mk a b) := i
  simp only
  cases a
  {
    unfold int_canon_repr
    simp only [Nat.zero_eq, true_or]
  }
  {
    case _ k =>
    cases b
    {
      unfold int_canon_repr
      simp only [Nat.succ_eq_add_one, Nat.add_eq_zero_iff, one_ne_zero, and_false, Nat.zero_eq, or_true]
    }
    {
      case _ k2 =>
      unfold int_canon_repr
      simp only
      apply canon_repr_eqn_2 (k,k2)
    }
  }
  termination_by i.1 + i.2

def IntNF := { n // IntNFCst n }

def pre_int_to_int_nf (n:PreInt): IntNF := by
  refine .mk ?_ ?_
  exact int_canon_repr n
  unfold IntNFCst
  exact canon_repr_eqn_2 n

def int_nf_to_pre_int (n:IntNF): PreInt := .mk (n.1.1) (n.1.2)

def eqn_87 (k:PreInt) : { j // int_canon_repr k = j } := by
  refine .mk ?_ ?_
  exact int_canon_repr k
  rfl

def c1 : Function.Injective int_nf_to_pre_int := by
  exact (Set.injective_codRestrict Subtype.property).mp fun ⦃a₁ a₂⦄ a => a

def canon_repr_red_eqn_1 : int_canon_repr (.mk 0 b) = (.mk 0 b) := by unfold int_canon_repr; simp

def canon_repr_red_eqn_2 : int_canon_repr (.mk a 0) = (.mk a 0) := by
  unfold int_canon_repr
  cases a -- ugh, case trees are annoying
  simp
  simp

def eqn_33 : ∀ (i : IntNF), pre_int_to_int_nf (int_nf_to_pre_int i) = i := by
  intro i
  let (.mk v p) := i
  unfold int_nf_to_pre_int pre_int_to_int_nf
  simp only
  congr
  unfold IntNFCst at p
  let (.mk a b) := v
  cases p
  {
    case _ h =>
    simp only at h; simp only
    rw [h]
    unfold int_canon_repr
    simp only [Nat.zero_eq]
  }
  {
    case _ h =>
    simp only at h; simp only
    rw [h]
    exact canon_repr_red_eqn_2
  }

example : wmap IntNF PreInt := by
  refine mkwmap ?_ ?_ ?_
  exact int_nf_to_pre_int
  exact pre_int_to_int_nf
  intro i
  exact eqn_33 i



def eq_tower (n:Nat)(A)(B) :=
  match n with
  | .zero => wmap A B
  | .succ a => wmap (eq_tower a A B) (eq_tower a A B)

def eq_tower_collapse : is_contr (eq_tower n A B) -> is_contr (eq_tower (n + 1) A B) := by
  intro c
  let x := contr_ty_to_contr_wmap c
  exact x

def loops (n)(T) := eq_tower n T T

def not_wmap : wmap Bool Bool := mkwmap not not (by intro; simp)

-- We define a predicate for "Has a Non-Identity Involution"
structure Involutive (T : Sort _) where
  w : wmap T T
  is_inv : wmap_trans w w = id_wmap
  not_id : w ≠ id_wmap

-- Base case: Level 0 (wmap Bool Bool)
def base_involution : Involutive Bool := by
  refine .mk ?_ ?_ ?_
  {
    exact not_wmap
  }
  {
    -- Verify involution: not ∘ not = id
    unfold wmap_trans id_wmap not_wmap
    dsimp
    simp only [Bool.not_not]
    rfl
  }
  {
    -- Verify not distinct from id
    intro h
    have h_val : not true = id true := by
      apply congrFun (congrArg (fun x => x.1.1) h) true
    simp only [Bool.not_true, id_eq, Bool.false_eq_true] at h_val
  }

-- Inductive Step
-- set_option pp.proofs true in
def step_involution {T : Sort _} (prev : Involutive T) : Involutive (wmap T T) := by
  let f_new : wmap (wmap T T) (wmap T T) := by
    refine mkwmap ?_ ?_ ?_
    { intro w; exact wmap_trans w prev.w } -- map w -> w ∘ f_prev
    { intro w; exact wmap_trans w prev.w } -- Inverse is same because f_prev is involution
    {
      intro w
      -- w ∘ f ∘ f = w ∘ id = w
      let (.mk m p1 p2) := prev
      dsimp
      unfold wmap_trans mkwmap
      reduce
      congr
      {
        funext k
        let p2 : (fun i => m.1.1 (m.1.1 i)) = id := by
          reduce at p1
          let k := psig_ext_rev p1
          dsimp at k
          simp only [PProd.mk.injEq] at k
          let (.intro fst _) := k
          reduce
          exact fst
        reduce at p2
        rw [funext_iff] at p2
        rw [p2 _]
      }
      {
        funext k
        let p2 : (fun i => m.1.2 (m.1.2 i)) = id := by
          reduce at p1
          let k := psig_ext_rev p1
          dsimp at k
          simp only [PProd.mk.injEq] at k
          let (.intro _ snd) := k
          reduce
          exact snd
        reduce at p2
        rw [funext_iff] at p2
        rw [p2 _]
      }
    }

  refine .mk f_new ?_ ?_
  {
    -- Show f_new ∘ f_new = id
    unfold wmap_trans id_wmap f_new
    reduce
    congr
    {
      funext i
      congr
      {
        funext k
        let (.mk m p1 p2) := prev
        let p2 : (fun i => m.1.1 (m.1.1 i)) = id := by
          reduce at p1
          let k := psig_ext_rev p1
          dsimp at k
          simp only [PProd.mk.injEq] at k
          let (.intro fst _) := k
          reduce
          exact fst
        reduce at p2
        rw [funext_iff] at p2
        rw [p2 _]
      }
      {
        funext k
        let (.mk m p1 p2) := prev
        let p2 : (fun i => m.1.2 (m.1.2 i)) = id := by
          reduce at p1
          let k := psig_ext_rev p1
          dsimp at k
          simp only [PProd.mk.injEq] at k
          let (.intro _ snd) := k
          reduce
          exact snd
        reduce at p2
        rw [funext_iff] at p2
        rw [p2 _]
      }
    }
    {
      funext k
      let (.mk m p1 p2) := prev
      reduce
      let p2 : (fun i => m.1.1 (m.1.1 i)) = id := by
        reduce at p1
        let k := psig_ext_rev p1
        dsimp at k
        simp only [PProd.mk.injEq] at k
        let (.intro fst _) := k
        reduce
        exact fst
      reduce at p2
      rw [funext_iff] at p2
      simp only [p2]
      let p2 : (fun i => m.1.2 (m.1.2 i)) = id := by
        reduce at p1
        let k := psig_ext_rev p1
        dsimp at k
        simp only [PProd.mk.injEq] at k
        let (.intro _ snd) := k
        reduce
        exact snd
      reduce at p2
      rw [funext_iff] at p2
      simp only [p2 _]
      rfl
    }
  }
  {
    -- Show f_new != id
    intro h
    -- If f_new = id, then f_new(id) = id
    have eval : f_new.1.1 id_wmap = id_wmap.1.1 id_wmap := by rw [h]
    dsimp [id_wmap, mkwmap] at eval
    -- LHS is id ∘ f_prev = f_prev
    -- RHS is id
    -- So f_prev = id
    -- But we know f_prev != id from hypothesis
    apply prev.not_id
    exact eval
  }

-- Recursively build the involution for level n
def mk_involution (n : Nat) : Involutive (eq_tower n Bool Bool) :=
  match n with
  | 0 => step_involution base_involution
  | n + 1 => step_involution (mk_involution n)

theorem level_n_not_contr (n : Nat) : is_contr (eq_tower n Bool Bool) -> False := by
  intro h_contr

  -- 1. Lift contractibility from T to (wmap T T)
  let wmap_is_contr := contr_ty_to_contr_wmap h_contr

  -- 2. Extract the single element (center) of the contractible wmap space
  let (.mk w_center w_all_eq) := wmap_is_contr

  -- 3. Retrieve our constructed distinct maps for this level
  let inv_struct := mk_involution n
  let f := inv_struct.w
  let id_map := id_wmap (T := eq_tower n Bool Bool)

  -- 4. Both f and id_map must be equal to the center
  have h_f_eq_center : f = w_center := w_all_eq f
  have h_id_eq_center : id_map = w_center := w_all_eq id_map

  -- 5. Therefore f must equal id_map
  rw [<-h_id_eq_center] at h_f_eq_center

  -- 6. This contradicts the property of our constructed involution
  exact inv_struct.not_id h_f_eq_center


@[reducible]
def cyclic (n)(f:A->A) := iterf n f = id

def not_cyclic : cyclic 2 not := by
  unfold cyclic
  funext i
  repeat unfold iterf
  simp only [id_eq, Bool.not_not]

def comp_limit (n): (iterf n not = id) ∨ (iterf n not = not) := by
  fun_induction (iterf n not)
  left; rfl
  case _ ih =>
  cases ih
  {
    case _ h =>
    simp only [h]
    right
    rfl
  }
  {
    case _ h =>
    simp only [h]
    left
    simp only [Bool.not_not]
    rfl
  }

example : cyclic 2 (fun (i:wmap Bool Bool) => wmap_trans i not_wmap) := by
  unfold cyclic
  repeat unfold iterf
  funext i
  let (.mk (.mk _ _) _) := i
  repeat unfold wmap_trans not_wmap
  simp only [id_eq, mkwmap_eqn_1, Bool.not_not]

def wmap_Bool_Bool_eq_dec (w : wmap Bool Bool) :
    PSum (w.1.1 true = true ∧ w.1.1 false = false) (w.1.1 true = false ∧ w.1.1 false = true) := by
  let x := wmap_left_injective w
  have ne : w.1.1 true ≠ w.1.1 false := by
    intro h;
    exact (Bool.eq_not_self true).mp (x (x (congrArg (w.1).fst h)))
  by_cases h : w.1.1 true = true
  · left
    constructor
    · exact h
    · simp_all
  · right
    constructor
    · exact eq_false_of_ne_true h
    · simp_all

def two_autos (w : wmap Bool Bool) : PSum (w = id_wmap) (w = not_wmap) := by
  let x := wmap_Bool_Bool_eq_dec w
  cases x with
  | inl h =>
    have hf : w.1.1 = id := funext (by simp [h])
    have hg : w.1.2 = id := by
      funext b
      rw [<-w.2 (w.1.2 b)]
      rw [hf]
      dsimp
      let (.mk (.mk f _) p) := w
      dsimp at p h hf
      dsimp
      cases b
      rw [<-h.2, p, <-h.2, p]
      rw [hf]
      rfl
      rw [<-h.1, p, <-h.1, p]
      rw [hf]
      rfl
    let (.mk (.mk f _) p) := w
    dsimp at hf hg
    subst hf
    subst hg
    left
    reduce
    congr
  | inr h =>
    have hf : w.1.1 = not := funext (by simp [h])
    have hg : w.1.2 = not := by
      funext b
      rw [<-w.2 (w.1.2 b)]
      rw [hf]
      let (.mk (.mk f _) p) := w
      dsimp at p h hf
      dsimp
      let k (i): Bool.not (f i) = f (Bool.not i) := by
        cases i <;> rw [hf]
      cases b
      {
        rw [<-h.1, p, <-h.2]
        rw [k]
        rw [p, hf]
        reduce
        rfl
      }
      {
        rw [<-h.2, p, <-h.1]
        rw [k, p, hf]
        reduce
        rfl
      }
    right
    let (.mk (.mk f _) p) := w
    dsimp at hf hg
    subst hf
    subst hg
    unfold not_wmap
    simp only [mkwmap_eqn_1]


def bool_to_wmap (i:Bool): wmap Bool Bool :=
  match i with
  | .true => id_wmap
  | .false => not_wmap

def wmap_to_bool (w : wmap Bool Bool) : Bool :=
  let x := two_autos w
  match x with
  | .inl _ => .true
  | .inr _ => .false

def bool_bool_aut_cancel (i:Bool): wmap_to_bool (bool_to_wmap i) = i := by
  cases i <;> reduce <;> rfl


def bool_bool_aut_wmap : wmap Bool (wmap Bool Bool) := by
  refine mkwmap ?_ ?_ ?_
  exact bool_to_wmap
  exact wmap_to_bool
  exact bool_bool_aut_cancel


def card_two_equiv : (wmap Bool Bool) ≃ Bool := by
  refine { toFun := ?_, invFun := ?_, left_inv := ?_, right_inv := ?_ }
  exact wmap_to_bool
  exact bool_to_wmap
  {
    refine Function.leftInverse_iff_comp.mpr ?_
    unfold Function.comp
    funext i
    simp [wmap_to_bool]
    let (.mk v p) := wtransp id_wmap (two_autos i)
    simp [id_wmap] at p
    rw [<-p]
    cases v
    {
      case _ p2 =>
      simp [bool_to_wmap]
      rw [p2]
    }
    {
      case _ p2 =>
      simp [bool_to_wmap]
      rw [p2]
    }
  }
  {
    unfold Function.RightInverse Function.LeftInverse
    intro i
    exact bool_bool_aut_cancel i
  }


def bool_aut_card_is_2 : Cardinal.mk (wmap Bool Bool) = Cardinal.mk (Fin 2) := by
  rw [Cardinal.mk_congr card_two_equiv]
  simp only [Cardinal.mk_fintype, Fintype.card_bool, Nat.cast_ofNat, Fintype.card_fin]


def acyclic (f:T->T) := ∀ i (_:i ≠ 0), iterf i f ≠ id

def nat_add_acyclic : acyclic (fun i => Nat.add i 1) := by
  intro i h h2
  cases k:i
  {
    subst k
    simp at h
  }
  rw [k] at h2
  reduce at h2
  rw [funext_iff] at h2
  let c := h2 0
  simp at c

structure Free (T:Sort _) where
  move : T -> T
  no_loops: ∀ i (_:i ≠ 0), iterf i move ≠ id

example : Free Nat := by
  refine { move := ?_, no_loops := ?_ }
  exact fun i => i + 1
  exact nat_add_acyclic


#check Quot.rec

def ExtEqFun (A)(B:A->Sort _) := Quot (@PointwiseEq A B)

def ext_fun_app (f:ExtEqFun A B)(x:A): B x := by
  refine f.lift ?_ ?_
  {
    intro f
    exact f x
  }
  {
    intro f h pweq
    exact pweq x
  }

example {A:Sort _}{B:A->Sort _}{f h:(a:A)->B a}(p:∀ i, f i = h i): f = h := by
  let qf : ExtEqFun _ _ := .mk _ f
  let qh : ExtEqFun _ _ := .mk _ h
  let x : ext_fun_app qf = ext_fun_app qh -> f = h := by
    intro ext
    unfold ext_fun_app qf qh at ext
    dsimp at ext
    eta_reduce at ext
    exact ext
  apply x
  let qfqh_eq : qf = qh := by
    unfold qf qh
    apply Quot.sound
    exact p
  rw [qfqh_eq]

def wmap_contr_fibs (w:wmap A B)(p:∀ i, w.1.1 (w.1.2 i) = i) : is_contr (fiber w.1.2 k) := by
  let x := wmap_left_injective w
  refine .mk ?_ ?_
  {
    refine .mk ?_ ?_
    exact w.1.1 k
    rw [w.2]
  }
  intro i
  let (.mk v p2) := i
  congr
  rw [<-p2, p v]

def fun_fun_contr_fibs (w:wmap (A → A) (A → A))(p:∀ i, w.1.1 (w.1.2 i) = i) : is_contr (fiber w.1.2 k) := by
  exact wmap_contr_fibs w p


def unit_wmap (c:is_contr T): wmap T PUnit := by
  refine .mk ?_ ?_
  {
    refine .mk ?_ ?_
    exact fun _ => .unit
    exact fun _ => c.1
  }
  intro i
  dsimp
  rw [<-c.2]

def unit_wmap_inv (c:is_contr T): wmap PUnit T := by
  refine wmap_invert (unit_wmap c) ?_
  {
    refine .mk ?_ ?_
    intro; exact .unit
    intro i
    cases i
    dsimp
  }

def contr_irrelevant_wmap {A:Sort _1}{B:Sort _2} (h1: is_contr A)(h2:is_contr B): wmap A B := by
  refine wmap_left_triangle_filler.{_, _, max _1 _2} ?_ ?_ ?_ ?_ (C:=PUnit)
  exact unit_wmap h1
  exact unit_wmap h2
  {
    let x := wmap_fun_map (arrow_fu A) (unit_wmap_inv h2)
    let v := wtransp x (fun _ => .unit)
    exact v.1
  }
  reduce
  intro _
  rfl

#print axioms contr_irrelevant_wmap

example {f:A->B}{h:B->A}(p:∀ i, h (f i) = i) : (fun i => h (f i)) = id := by
  let k : wmap A A := by
    refine mkwmap id (fun i => h (f i)) ?_
    intro i
    dsimp
    apply p i
  let x : wmap (A->A) (A->A) := by
    exact s442_2 k
  let m := wtransp x id
  exact m.2


example : Real.sqrt ((1:Real)/2) = (Real.sqrt 2)/2 := by
  let x : invertible (fun i => (i:Real) * 2) := by
    refine .mk (fun i => i / 2) ?_
    exact fun i => mul_div_cancel_of_invertible i 2
  apply invertible_to_injective x
  simp only [isUnit_iff_ne_zero, ne_eq, OfNat.ofNat_ne_zero,
    not_false_eq_true, IsUnit.div_mul_cancel]
  let x2 : 2 = Real.sqrt (2^2) := by
    refine Eq.symm (Real.sqrt_sq ?_)
    exact zero_le_two
  rw (occs := [2]) [x2]
  let x3 : ∀ a b (_:a>0)(_:b>0), (Real.sqrt a) * (Real.sqrt b) = Real.sqrt (a * b) := by
    intro a b h1 h2
    refine Eq.symm (Real.sqrt_mul' a ?_)
    exact Std.le_of_lt h2
  rw [x3 _ _ (by grind) (by grind)]
  let x4 : (2:Real) ^ 2 = 2 * 2 := by
    exact pow_two 2
  rw [x4]
  let x5 : ((1:Real)/2) * (2 * 2) = 2 := by
    simp only [one_div, ne_eq, OfNat.ofNat_ne_zero, not_false_eq_true, inv_mul_cancel_left₀]
  rewrite [x5]
  trivial


def rot2_tower (n): Equiv Bool (loops n Bool) := by
  induction n
  case zero =>
    unfold loops eq_tower
    exact card_two_equiv.symm
  case succ n ih =>
    let L := loops n Bool
    let f_L := ih.1
    let g_L := ih.2
    let p_L := ih.3
    let q_L := ih.4
    let conj_inv (phi : wmap Bool Bool) : wmap L L := by
      refine mkwmap ?_ ?_ ?_
      exact (fun l => f_L (phi.1.1 (g_L l)))
      exact (fun l => f_L (phi.1.2 (g_L l)))
      intro l
      reduce; reduce at p_L
      rw [p_L]
      let x := phi.2
      reduce at x
      rw [x]
      reduce at q_L
      rw [q_L]
    let conj (w : wmap L L) : wmap Bool Bool := by
      refine mkwmap ?_ ?_ ?_
      exact (fun b => g_L (w.1.1 (f_L b)))
      exact (fun b => g_L (w.1.2 (f_L b)))
      intro l
      reduce; reduce at p_L q_L
      let x := w.2
      reduce at x
      rw [q_L, x, p_L]
    refine {
      toFun := (fun b => conj_inv (bool_to_wmap b)),
      invFun := (fun w => wmap_to_bool (conj w)),
      left_inv := ?_,
      right_inv := ?_
    }
    {
      intro b
      cases b <;> dsimp <;>
      {
        unfold bool_to_wmap conj_inv conj not_wmap g_L f_L
        simp only [mkwmap_eqn_1, Equiv.toFun_as_coe, Equiv.invFun_as_coe, Equiv.symm_apply_apply]
        reduce
        trivial
      }
    }
    {
      refine Function.LeftInverse.rightInverse ?_
      intro x
      dsimp
      let x2 := card_two_equiv.3
      unfold Function.LeftInverse card_two_equiv at x2
      dsimp at x2
      rw [x2]
      reduce; reduce at p_L q_L
      simp only [Equiv.toFun_as_coe, Equiv.invFun_as_coe, Equiv.apply_symm_apply, PProd.mk.eta]
      congr
    }

@[reducible]
def S3 := Equiv.Perm (Fin 3)

-- Define the transposition (0 1)
def σ : S3 := Equiv.swap 0 1

def τ : S3 := by
  unfold S3
  refine .mk ?_ ?_ ?_ ?_
  {
    intro i
    exact i + 1
  }
  {
    intro i
    exact i - 1
  }
  exact leftInverse_sub_add_left 1
  refine Function.rightInverse_of_injective_of_leftInverse ?_ ?_
  exact sub_left_injective
  exact leftInverse_sub_add_left 1

-- Compute σ * τ (composition σ ∘ τ)
lemma σ_mul_τ_apply_zero : (σ * τ) 0 = 0 := by
  simp only [Fin.isValue, Equiv.Perm.coe_mul, Function.comp_apply]
  reduce
  rfl

lemma τ_mul_σ_apply_zero : (τ * σ) 0 = 2 := by
  simp only [Fin.isValue, Equiv.Perm.coe_mul, Function.comp_apply]
  reduce
  rfl

-- -- They differ at 0, so σ * τ ≠ τ * σ
lemma σ_mul_τ_ne_τ_mul_σ : σ * τ ≠ τ * σ :=
  fun h => by
    let p : (σ * τ) 0 = (τ * σ) 0 := congrFun (congrArg _ h) 0
    reduce at p
    simp only [Fin.zero_eta, Fin.isValue, Fin.reduceFinMk, Fin.reduceEq] at p

-- Thus S3 is not abelian
theorem S3_not_abelian : ¬ ∀ (g h : S3), g * h = h * g :=
  fun h => σ_mul_τ_ne_τ_mul_σ (h σ τ)



structure FunctorialS (F:Sort _ -> Sort _) where
  map : (wmap A B) -> (F A -> F B)
  map_id : ∀ (x : F A), map (id_wmap) x = x
  map_comp : ∀ (f : wmap A B) (g : wmap B C) (x : F A),
    map (wmap_trans f g) x = (map g) (map f x)

structure FunctorialE (F:Sort _ -> Sort _) where
  map : (Equiv A B) -> (F A -> F B)
  map_id : ∀ (x : F A), map (Equiv.refl _) x = x
  map_comp : ∀ (f : Equiv A B) (g : Equiv B C) (x : F A),
    map (Equiv.trans f g) x = (map g) (map f x)

structure FunctorialH (R:Sort _->Sort _->Sort _) (F:Sort _->Sort _) where
  map: R A B -> (F A -> F B)
  rel_id: R T T
  map_id: ∀ (x:F A), map (rel_id) x = x
  rel_comp: R A B -> R B C -> R A C
  map_comp: ∀ (f:R A B)(g:R B C)(x:F A),
    map (rel_comp f g) x = (map g) (map f x)

set_option linter.unusedVariables false in
@[reducible]
def FunctorialG2 (R:Sort _->Sort _->Sort _) (F:Sort _->Sort _) :=
  (map: ∀ {A B}, R A B -> (F A -> F B)) ×'
  (rel_id: ∀ {T}, R T T) ×'
  (map_id: ∀ {A}(x:F A), map rel_id x = x) ×'
  (rel_comp: ∀ {A B C}, R A B -> R B C -> R A C) ×'
  (∀ {A B C}(f:R A B)(g:R B C)(x:F A), map (rel_comp f g) x = (map g) (map f x))

def wmap_fu_ (A): FunctorialH wmap (fun T => wmap A T) := by
  refine { map := ?_, rel_id := ?_, map_id := ?_, rel_comp := ?_, map_comp := ?_ }
  {
    intro _ _ w1 w2
    exact wmap_trans w2 w1
  }
  {
    intro _; exact id_wmap
  }
  {
    intro _ w
    rfl
  }
  {
    intro _ _ _ w1 w2
    exact wmap_trans w1 w2
  }
  {
    intro _ _ _ w1 w2 w3
    rfl
  }

-- def wmap_fun_map_2_ (fu : FunctorialG wmap F)(w : wmap A B) : wmap (F A) (F B) := by
--   refine mkwmap (fu.map w) ?_ ?_

def wmap_fu (A): FunctorialS (fun T => wmap A T) := by
  refine { map := ?_, map_id := ?_, map_comp := ?_ }
  {
    intro X B f w
    refine mkwmap ?_ ?_ ?_
    {
      intro a
      let x := wmap_trans w f
      exact x.1.1 a
    }
    {
      intro b
      let x := f.1.2 b |> w.1.2
      exact x
    }
    intro a
    reduce
    let x := f.2
    reduce at x
    rw [x]
    let x := w.2
    reduce at x
    rw [x]
  }
  {
    intro B w
    reduce
    rfl
  }
  {
    intro A B C f g w
    rfl
  }


def equiv_to_wmap (e:Equiv A B) : wmap A B :=
  mkwmap e.1 e.2 e.3

def wmap_fun_map_2 (fu : FunctorialS F)(w : Equiv A B) : wmap (F A) (F B) := by
  refine mkwmap (fu.map (equiv_to_wmap w)) (fu.map (equiv_to_wmap w.symm)) ?_
  intro i
  rw [<-fu.map_comp]
  reduce
  simp
  let x := fu.map_id i
  reduce at x
  apply x

def equiv_fun_map (fu : FunctorialS F)(w : Equiv A B) : Equiv (F A) (F B) := by
  refine { toFun := ?_, invFun := ?_, left_inv:=?_, right_inv:=?_}
  { exact fu.map (equiv_to_wmap w) }
  { exact fu.map (equiv_to_wmap w.symm) }
  {
    intro fa
    rw [<- @FunctorialS.map_comp]
    have x : wmap_trans (equiv_to_wmap w) (equiv_to_wmap w.symm) = id_wmap := by
      reduce
      simp only [Equiv.invFun_as_coe, Equiv.toFun_as_coe, Equiv.symm_apply_apply, implies_true, id_eq,
        shift_tr_fun_g]
    rw [x]
    exact fu.map_id fa
  }
  {
    intro fb
    rw [<- @FunctorialS.map_comp]
    have x : wmap_trans (equiv_to_wmap w.symm) (equiv_to_wmap w) = id_wmap := by
      reduce
      simp only [Equiv.toFun_as_coe, Equiv.invFun_as_coe, Equiv.apply_symm_apply, implies_true, id_eq,
        shift_tr_fun_g]
    rw [x]
    exact fu.map_id fb
  }


#print axioms wmap_fun_map_2

def wsubst3 (fB : Equiv B B') : wmap (wmap A B) (wmap A B') :=
  wmap_fun_map_2 (wmap_fu A) fB

-- def wmap_fun_map_3 (fu : FunctorialG2 wmap F)(w : Equiv A B) : wmap (F A) (F B) := by
--   let ⟨ map, id_, map_id, comp, map_comp ⟩ := fu
--   refine mkwmap ?_ ?_ ?_
--   {
--     intro fa
--     let x := map (equiv_to_wmap w) fa
--     exact x
--   }
--   {
--     intro fb
--     let x := map (equiv_to_wmap w.symm) fb
--     exact x
--   }
--   {
--     intro fa
--     rw [← map_comp]
--     admit
--   }

def prop_unit (T:Prop): is_unit T := by
  intro _ _
  rfl

def unit_contr : is_contr Unit := by
  refine .mk .unit ?_
  intro i
  cases i
  rfl

def unit_contr_p : is_contr PUnit := by
  refine .mk .unit ?_
  intro i
  cases i
  rfl

def h517 (c1:is_contr A)(c2:is_contr B): wmap (wmap A B) (wmap Unit Unit) := by
  refine mkwmap ?_ ?_ ?_
  {
    intro _
    exact id_wmap
  }
  {
    intro w
    exact contr_irrelevant_wmap c1 c2
  }
  intro w
  let (.mk (.mk f h) p) := w
  let (.mk cc1 cp1) := c1
  let (.mk cc2 cp2) := c2
  reduce
  congr
  {
    funext i
    rw [cp2 (f i)]
  }
  {
    funext i
    rw [cp1 (h i)]
  }

def Not2 (T) := T -> Empty
example : Not2 Unit ≃ Empty := by
  refine { toFun := ?_, invFun := ?_, left_inv := ?_, right_inv := ?_ }
  {
    intro f
    exact f .unit
  }
  {
    intro i
    exact Empty.elim i
  }
  {
    refine Function.leftInverse_iff_comp.mpr ?_
    funext i
    dsimp
    generalize i () = k
    exact Empty.elim k
  }
  {
    refine Function.rightInverse_iff_comp.mpr ?_
    funext i
    exact Empty.elim i
  }
example : Not2 Empty ≃ Unit := by
  refine { toFun := ?_, invFun := ?_, left_inv := ?_, right_inv := ?_ }
  {
    intro _
    exact .unit
  }
  {
    intro _ e
    exact Empty.elim e
  }
  {
    refine Function.leftInverse_iff_comp.mpr ?_
    funext _
    dsimp
    funext i
    exact Empty.elim i
  }
  {
    exact Function.LeftInverse.rightInverse (congrFun rfl)
  }

def eq_contr_2 {A : Sort _} (x y : A) (c : is_contr A) : is_contr (x = y) := by
  let p : x = y := (c.2 x).trans (c.2 y).symm
  refine .mk p ?_
  intro q
  subst q
  exact eq_centr_refl

def fiber_contr_on_contr_tys {A B : Sort _}
  (h : B → A) (cB : is_contr B) (cA : is_contr A) (a : A)
: is_contr (fiber h a)
:= by
  let ccB := cB.1
  let ccA := cA.1
  let p_h : h ccB = ccA := cA.2 (h ccB)
  let p_a : a = ccA := cA.2 a
  let p : h ccB = a := p_h.trans p_a.symm
  refine .mk (.mk ccB p) ?_
  intro (.mk b e)
  let p_b : b = ccB := (cB.2 ccB).trans (cB.2 b).symm |>.symm
  congr


def PropMapFu := ∀ P:Prop->Prop, Functorial P

example (K:PropMapFu): False := by
  let x := K (Not)
  let x2 := x.map (A:=False) (B:=True)
  let x3 := x2 False.elim
  simp only [not_false_eq_true, not_true_eq_false] at x3
  exact x3 .intro

def prop_map_fu_2 : FunctorialS (fun P => P -> Prop) := by
  refine { map := ?_, map_id := ?_, map_comp := ?_ }
  {
    intro A B w P b
    exact P (w.1.2 b)
  }
  {
    intro A P
    funext i
    reduce
    rfl
  }
  {
    intro A B C w1 w2 P
    funext i
    reduce
    rfl
  }

def eq_fu (A:Sort _): FunctorialH (Eq) (fun T => A = T) := {
  map := by {
    intro B C eq1 eq2
    rw [eq2, eq1]
  },
  rel_id := by {
    intro _
    rfl
  },
  map_id := by {
    intro B eq
    cases eq
    dsimp
  },
  rel_comp := by {
    intro A B C eq1 eq2
    rw [eq1, eq2]
  },
  map_comp := by {
    intro _ _ _ eq1 eq2 eq3
    rfl
  }
}

def fun_map_g (fu:FunctorialH R F)(r:R A B): F A -> F B := fu.map r

def map_on_contr_equiv (f:A->B)(c1:is_contr A)(c2:is_contr B): is_equiv f := by
  intro i
  refine .mk ?_ ?_
  {
    refine .mk (c1.1) ?_
    rw [c2.2 i, c2.2 (f c1.1)]
  }
  {
    intro a
    let (.mk v p) := a
    congr
    rw [c1.2 v]
  }

def weak_is_equiv (f:A->B) := ∀ i:B, is_unit (fiber f i)
def weq_weak (A:Sort _)(B:Sort _) := (f:A->B) ×' weak_is_equiv f
set_option pp.proofs true in
def uvp2 (A B:Prop): weq_weak (A = B) (wmap A B) := by
  refine .mk ?_ ?_
  {
    intro eq
    refine mkwmap ?_ ?_ ?_
    {
      intro i; exact cast eq i
    }
    {
      intro i; exact cast eq.symm i
    }
    {
      intro i
      exact cast_eq rfl i
    }
  }
  intro w q1 q2
  let (.mk (.mk f h) p) := w
  reduce at p
  let (.mk v1 p2) := q1
  let (.mk v2 p3) := q2
  congr

#print axioms uvp2

-- def h518_2 {A B:Prop} (c1:is_contr A)(c2:is_contr B): weq (A = B) (wmap A B) := by
--   refine .mk ?_ ?_
--   {
--     intro eq
--     -- cases eq
--     exact mkwmap (fun i => cast eq i) (fun i => cast eq.symm i) (fun _ => by cases eq; dsimp)
--   }
--   let x := h517 c1 c2
--   let w_contr : is_contr (wmap A B) := by
--     refine h437_2 x ?_
--     refine contr_ty_to_contr_wmap ?_
--     exact unit_contr
--   refine map_on_contr_equiv _ ?_ w_contr
--   refine h437_2 ?_ unit_contr
--   refine mkwmap (fun _ => .unit) (fun _ => Classical.choice ?_) (fun _ => proof_irrel _ _)


-- --   admit

-- #print axioms h518_2

-- def h518_3 {A B:Prop} (c1:is_contr A)(c2:is_contr B): weq (Eq2 A B) (wmap A B) := by
--   refine .mk ?_ ?_
--   {
--     intro q
--     refine Quot.liftOn q ?_ ?_
--     {
--       intro preq
--       cases preq
--       exact id_wmap
--       case _ w =>
--       exact weq_to_wmap (weq_inverse w)
--     }
--     intro q1 q2 p
--     cases q1
--     cases q2
--     reduce at p
--     reduce; rfl
--     case _ w =>
--       reduce; rfl
--     case _ w =>
--       reduce; rfl
--   }
--   dsimp
--   refine map_on_contr_equiv _ ?_ (h437_2 (h517 c1 c2) (contr_ty_to_contr_wmap unit_contr))
--   refine h437_2 ?_ unit_contr
--   refine mkwmap (fun _ => .unit) (fun _ => ?_) (fun _ => ?_)
--   {
--     refine Eq2.path ?_
--     refine .mk (fun _ => c2.1) ?_
--     exact map_on_contr_equiv _ c1 c2
--   }
--   case _ x =>
--   refine Quot.liftOn x ?_ ?_
--   {
--     intro q
--     cases q
--     . dsimp
--       unfold Eq2.path
--       let (.intro _ p) := Quot.exists_rep x
--       rw [<-p]
--       apply Quot.sound
--       case _ w =>
--       cases w
--       reduce
--       rfl
--       case _ w =>
--       cases w
--       reduce
--       intro _; exact proof_irrel _ _
--     .
--       case _ w =>
--       dsimp
--       unfold Eq2.path
--       let (.intro _ p) := Quot.exists_rep x
--       rw [<-p]
--       apply Quot.sound
--       case _ w =>
--       cases w
--       reduce
--       rfl
--       reduce
--       intro _; exact proof_irrel _ _
--   }
--   intro a b r
--   cases a
--   cases b
--   repeat rfl


-- def h520 (c1:is_contr A)(c2:is_contr B): A = B := by
--   let w := contr_irrelevant_wmap c1 c2
--   exact h518_2 c1 c2 w

inductive IsSort : {T:Sort _} -> T -> Prop
  | intro (S:Sort _) : IsSort S

def IsValue (T:k) := (IsSort T) -> False

axiom x_of_nat_are_values (n:Nat): IsSort n = False

example : IsValue 0 := by
  intro k
  -- nomatch k
  let _ : IsSort 0 = False := by
    exact x_of_nat_are_values 0
  grind

inductive KnownType : Sort _ -> Sort _
  | arrow (A:Sort _)(B:A->Sort _)(_:KnownType A)(_:∀ i, KnownType (B i)) : KnownType ((a:A)->B a)
  | dpair (A:Sort _)(B:A->Sort _)(_:KnownType A)(_:∀ i, KnownType (B i)) : KnownType ((a:A) ×' B a)
  | oneof (A:Sort _)(B:Sort _)(_:KnownType A)(_:KnownType B) : KnownType (PSum A B)
  | pt : KnownType PUnit



-- def cast_eqn_1 {P:A->Sort _}{p:P v}(eq:A=B)(eq2:@PSigma A P = @PSigma B (fun i => P (cast eq.symm i)))
-- : cast eq2 (@PSigma.mk A P v p) = @PSigma.mk B (fun i => P (cast eq.symm i)) (cast eq v) (by dsimp; rw [@cast_cast]; rw [cast_eq]; exact p)
-- := by
--   simp only [cast_eq, eq_mpr_eq_cast, id_eq]
--   refine PSigma.ext ?_ ?_
--   rw [cast_eqn_1]
--   rw [cast_eqn_1]
--   dsimp
--   rfl

def wmap_dep_pair (w:wmap A B): wmap (@PSigma A P) (@PSigma B fun i => P (w.1.2 i)) := by
  refine mkwmap ?_ ?_ ?_
  {
    intro (.mk v p)
    refine .mk (w.1.1 v) ?_
    rw [w.2]
    exact p
  }
  {
    intro (.mk v p)
    refine .mk (w.1.2 v) ?_
    exact p
  }
  {
    intro (.mk v p)
    dsimp
    congr
    rw [w.2]
    exact cast_heq (Eq.symm (congrArg P (w.2 v))) p
  }

def wmap_dep_arrow {P:A->Sort _}(w:wmap A B): wmap (∀ i:A, P i) (∀ i:B, P (w.1.2 i)) := by
  refine mkwmap ?_ ?_ ?_
  {
    intro f b
    exact f (w.1.2 b)
  }
  {
    intro f a
    let x := f (w.1.1 a)
    rw [w.2] at x
    exact x
  }
  {
    intro f
    dsimp
    funext i
    refine cast_eq_iff_heq.mpr ?_
    rw [w.2]
  }

example := by
  let k := wmap_dep_pair list_nat (P:=fun i=> i.isEmpty)
  apply k.1.2
  refine .mk 0 ?_
  reduce
  rfl

def id_equiv : Equiv T T := by
  refine { toFun := ?_, invFun := ?_, left_inv := ?_, right_inv := ?_ }
  { exact id }
  { exact id }
  exact Function.RightInverse.leftInverse (congrFun rfl)
  exact Function.rightInverse_of_injective_of_leftInverse (fun _ _ a => a) (congrFun rfl)

def pair_fu_1 (B): Functorial fun T => T × B := by
  refine { map := ?_, map_id := ?_, map_comp := ?_ }
  {
    intro A C f (.mk a b)
    refine .mk (f a) (b)
  }
  {
    intro A f; dsimp
  }
  {
    intro A C D f h (.mk a b)
    dsimp
  }

def pair_fu_2 (A) : Functorial fun T => A × T := by
  refine { map := ?_, map_id := ?_, map_comp := ?_ }
  {
    intro A C f (.mk a b)
    refine .mk a (f b)
  }
  {
    intro A f; dsimp
  }
  {
    intro A C D f h (.mk a b)
    dsimp
  }

def dpair_fu_ex : FunctorialS fun T => (P:T->Sort _) ×' (i:T) ×' P i := by
  refine { map := ?_, map_id := ?_, map_comp := ?_ }
  {
    intro A B w (.mk P p)
    refine .mk ?_ ?_
    {
      intro b; apply P; exact w.1.2 b
    }
    {
      refine .mk ?_ ?_
      exact w.1.1 p.1
      reduce
      let x := w.2 p.1
      reduce at x
      rw [x]
      exact p.2
    }
  }
  {
    intro A (.mk P p)
    reduce
    congr
  }
  {
    intro A B C w1 w2 (.mk P p)
    reduce
    repeat rw [@eqRec_eq_cast, ]
    simp only [cast_cast, PSigma.mk.injEq, heq_eq_eq, true_and]
    rfl
  }

def darrow_fu : FunctorialH Equiv fun T => ∀ P:T->Sort _, (i:T) -> P i := by
  refine { map := ?_, rel_id := ?_, map_id := ?_, rel_comp := ?_, map_comp := ?_ }
  {
    intro A B w K P b
    let x := K (fun i => P (w.1 i)) (w.2 b)
    rw [w.4] at x
    exact x
  }
  {
    intro _; exact id_equiv
  }
  {
    intro A K
    reduce
    eta_reduce
    eta_reduce
    rfl
  }
  {
    intro A B C e1 e2
    exact Equiv.trans e1 e2
  }
  {
    intro A B C e1 e2 K
    funext P c
    reduce
    repeat rw [@eqRec_eq_cast]
    rw [cast_cast]
    congr
  }

#print axioms darrow_fu

axiom psigma_cast_redn_1_ax {P1 P2:T->Sort _}{p1:P1 v1}{p2:P2 v2}:
  @HEq ((i : T) ×' P1 i) ⟨v1, p1⟩ ((i : T) ×' P2 i) ⟨v2, p2⟩
  -> v1 = v2 ∧ @HEq (P1 v1) p1 (P2 v2) p2

-- example (e:List Unit ≃ Nat): @List.nil Unit = sorry := by
--   -- let w := wmap_fun_map sigma_fu list_nat
--   -- let _ := wtransp w
--   let e := by
--     refine wmap_to_weq list_nat ?_
--     refine .mk ?_ ?_
--     exact list2nat
--     intro i
--     exact nl_coh i
--   let k := wtransp weq_is_iso e
--   let c := iso_to_equiv k.1
--   let w := wmap_fun_map_2 sigma_fu_ex c.symm
--   let x := by
--     refine wtransp w ⟨ fun i=>i.isEmpty, ?_, ?_ ⟩
--     exact []
--     reduce
--     rfl
--   let (.mk (.mk P (.mk v _)) p) := x
--   -- reduce at p
--   unfold w wmap_fun_map_2 sigma_fu_ex at p;
--   dsimp at p;
--   simp only [PSigma.mk.injEq, List.isEmpty_iff] at p
--   let (.intro l r) := p
--   reduce at l
--   reduce at r
--   let (.intro l _) := psigma_cast_red_1_ax r

--   let _ := by
--     refine shift_tr_fun_g ?_ l (h:=list2nat)
--     intro i
--     exact nl_coh i

--   rw [<-l]

inductive KnownEq.{u} : {A B:Type u} -> A -> B -> Type (u+1)
  | trv : KnownEq x x
  | fn (A:Type u)(F:A->Type u)(f h:(x:A)->F x)(eq: (x:A) -> KnownEq (f x) (h x)): KnownEq f h
  | pair (A:Type u)(F:A->Type u)(v1:A)(p1:F v1)(v2:A)(p2:F v2)(_:KnownEq v1 v2)(_:KnownEq p1 p2): KnownEq (@Sigma.mk A F v1 p1) (@Sigma.mk A F v2 p2)


example : KnownEq (fun i:Nat=> i + 0) (fun i:Nat=> 0 + i) := by
  refine KnownEq.fn ℕ (fun x => ℕ) (fun i => i + 0) (fun i => 0 + i) ?_
  intro x
  dsimp
  rw [Nat.zero_add]
  exact KnownEq.trv

def NumBase := { base:Nat // base > 1 }
def Tm (base:NumBase) := { tm:Nat // tm < base.1 }
def TmNum (base:NumBase) := List (Tm base)

def as_term_seqv (n:Nat)(base:NumBase): TmNum base :=
  let (.mk b e) := base
  let d := n / b;
  let rem := n - d * b;
  if h:n = 0 then .nil
  else by
    refine .cons (.mk rem ?_) (as_term_seqv d (.mk b e))
    unfold rem d; dsimp
    rw [← @Nat.mod_eq_sub_div_mul]
    refine Nat.mod_lt n ?_
    exact Nat.zero_lt_of_lt e
  decreasing_by
    refine Nat.div_lt_self ?_ e
    exact Nat.zero_lt_of_ne_zero h

def as_nat_rec (base:NumBase)(tms:TmNum base)(ix:Nat): Nat :=
  match tms with
  | .cons (.mk tm _) t =>
    let b := base.1
    let k := b ^ ix;
    tm * k + (as_nat_rec base t (ix+1))
  | .nil => 0
def as_nat (base:NumBase)(tms:TmNum base): Nat :=
  as_nat_rec base tms 0

def tm_num_one (base:NumBase): TmNum base :=
  .cons (.mk 1 (by grind)) .nil

def tm_num_zero (base:NumBase): TmNum base :=
  .nil

def base_2 : NumBase := .mk 2 (by grind)
def t := as_term_seqv 1 base_2

#reduce t
#reduce as_nat base_2 t

def tm_num_add_rec (base:NumBase)(a b:TmNum base)(c:Bool): TmNum base :=
  match a, b with
  | .cons (.mk ta p1) a_t, .cons (.mk tb p2) b_t => by
    let k := ta + tb + if c then 1 else 0
    let t := k % base.1
    refine .cons (.mk t ?_) ?_
    {
      refine Nat.mod_lt k ?_
      exact Nat.zero_lt_of_lt p1
    }
    let cc := k >= base.1;
    exact tm_num_add_rec base a_t b_t cc
  | .cons (.mk ta p1) a_t, .nil => by
    let k := ta + if c then 1 else 0
    let t := k % base.1
    refine .cons (.mk t ?_) ?_
    {
      refine Nat.mod_lt k ?_
      exact Nat.zero_lt_of_lt p1
    }
    let cc := k >= base.1
    exact tm_num_add_rec base a_t .nil cc
  | .nil, .cons (.mk tb p2) b_t => by
    let k := tb + if c then 1 else 0
    let t := k % base.1
    refine .cons (.mk t ?_) ?_
    {
      refine Nat.mod_lt k ?_
      exact Nat.zero_lt_of_lt p2
    }
    let cc := k >= base.1
    exact tm_num_add_rec base .nil b_t cc
  | .nil, .nil =>
    if c then tm_num_one base else .nil
  termination_by a.length + b.length


def tm_num_add (base:NumBase)(a b:TmNum base) :=
  tm_num_add_rec base a b .false

def ov_term (base:NumBase): Nat := base.1 - 1

-- def tm_num_add_inverse_tail (base:NumBase)(n:TmNum base): TmNum base :=
--   match n with
--   | .cons (.mk v p) t =>
--     let ov_tm := ov_term base
--     let tm : Tm base := by
--       refine .mk (ov_tm - v) ?_
--       refine Nat.sub_lt_of_lt ?_
--       unfold ov_tm ov_term
--       exact Nat.sub_one_lt_of_lt p
--     .cons tm (tm_num_add_inverse_tail base t)
--   | .nil => .nil

-- def tm_num_add_inverse (base:NumBase)(n:TmNum base): TmNum base :=
--   tm_num_add _ (tm_num_one base) (tm_num_add_inverse_tail _ n)


-- -- example : tm_num_add base_2 t t = sorry := by
-- --   reduce
-- --   unfold tm_num_add_rec

-- -- example : (tm_num_add base_2 t t |> as_nat base_2) = sorry := by
-- --   reduce
-- --   repeat unfold as_term_seqv tm_num_add_rec as_nat_rec; dsimp
-- --   unfold tm_num_one; dsimp
-- --   unfold as_nat_rec; dsimp


-- def wle (A B : Type u) : Prop := Nonempty (wmap A B)

-- def wle_refl (A : Type u) : wle A A := ⟨id_wmap⟩
-- def wle_trans {A B C : Type u} :
--   wle A B → wle B C → wle A C :=
-- by
--   intro (.intro f) (.intro g)
--   refine .intro ?_
--   exact wmap_trans f g

-- instance ty_preorder_inst : Preorder (Type _) where
--   le := wle
--   le_refl := wle_refl
--   le_trans := by
--     intro A B C
--     exact wle_trans

-- def ty_lat_bot (p:Inhabited T): Unit ≤ T := by
--   refine .intro ?_
--   refine mkwmap ?_ ?_ ?_
--   {
--     intro _
--     exact p.default
--   }
--   {
--     intro _
--     exact .unit
--   }
--   intro; rfl


-- example {n} : path n (0 + n) := by
--   induction n
--   {
--     dsimp; exact id_path _
--   }
--   case _ k ih =>
--   exact map_on_paths (fun P a => a) (path (k + 1)) fun P => ih fun k => P (k + 1)

-- set_option pp.proofs true in
-- def path_contr {T:Sort _}(i:T): is_contr (path i i) := by
--   let cc := id_path i
--   refine .mk cc ?_
--   intro p
--   funext P v
--   reduce

--   dsimp at x

-- def parm {i:A}(p:path i i): p = id_path i := by
--   let x := contr_ty_vals_irrel (path_contr i)
--   let x2 := x p (id_path i)
--   exact x2

-- -- def path_J {A : Sort _} {a : A}
-- --   (P : (b : A) → path a b → Sort _)
-- --   (h : P a (id_path a))
-- --   {b : A} (p : path a b) : P b p := by
-- --   let F : A → Sort _ :=
-- --     fun x => (q : path a x) → P x q
-- --   have base : F a :=
-- --     fun q => by
-- --       have q_is_refl : q = id_path a := parm _
-- --       rw [q_is_refl]
-- --       exact h
-- --   exact p F base p

-- -- def path_subst_2 {A : Sort _} {a b : A} (P : A -> Sort _) (p : path a b) (x : P a) : P b :=
-- --   path_J (fun y _ => P y) x p


def squashing_rel_path : wmap_fiber_thining_rel (eq_is_path a b) = fun _ _ => True := by
  reduce
  simp

example {A:Sort u1}{a b:A}: (Quot (wmap_fiber_thining_rel (eq_is_path a b))) = Squash (path.{_, u1} a b) := by
  conv =>
    arg 2; unfold Squash Quotient Setoid.trivial
  simp [squashing_rel_path]

def Eq.subst' {a b:A}(e:Eq a b)(P:A->Sort _)(v:P a): P b :=
  Eq.rec v e

def eq_subst_inj (a b:A)(P): Function.Injective fun i:Eq a b => Eq.subst' i P := by
  exact Function.injective_of_subsingleton _


-- def subst_on_same_paths_indis {A : Sort _} {a b : A} {p1 p2 : path a b} {P : A → Sort _} {pa : P a} : path_subst P p1 pa = path_subst P p2 pa := by
--   admit

-- def same_paths_indis {A : Sort _} {a b : A} {p1 p2 : path a b} : (p1 ≠ p2) → False := by
--   intro h1
--   apply h1
--   funext P pa
--   exact subst_on_same_paths_indis

example : ((p1 ≠ p2) → False) -> (p1 = p2) := Classical.byContradiction

-- example {A:Sort u1}{a b:A} : wmap (path.{_, u1} a b) (Squash (path.{_, u1} a b)) := by
--   refine mkwmap (Quot.mk _) ?_ ?_
--   {
--     intro q P pa
--     refine Quot.recOn q ?_ ?_
--     {
--       intro p
--       exact path_subst P p pa
--     }
--     intro p1 p2 rel
--     simp only [eq_rec_constant]
--     exact subst_on_same_paths_indis
--   }
--   intro p
--   reduce
--   rfl


def NatP (T:Sort _) := PSum Unit (Unit × T)


-- inductive NSNat | zero | suc (_:Unit -> NSNat) deriving Nonempty, Inhabited


-- -- partial def ns_omega_i (_:Unit): { i:NSNat // ∃ k, i = (.suc k) } := by
-- --   refine .mk (.suc ?_) ?_
-- --   {
-- --     intro k
-- --     let x := (ns_omega_i k).1
-- --     exact x
-- --   }
-- --   refine .intro ?_ ?_
-- --   {
-- --     intro k
-- --     let x := (ns_omega_i k).1
-- --     exact x
-- --   }
-- --   dsimp


-- -- def ns_omega := ns_omega_i .unit

-- def ListP (I:Sort _)(R:Sort _) := PSum Unit (I × R)
-- def AltList (T:Type)(i) := iterf (i + 1) (ListP T) Empty

-- def list_to_alt_list (l:List Nat): AltList Nat (l.length) :=
--   match l mapith
--   | .nil => .inl .unit
--   | .cons n t => .inr (.mk n (list_to_alt_list t))

-- def summ (i)(p:AltList Nat i): Nat :=
--   match i with
--   | .zero => default
--   | .succ a =>
--     match p with
--     | .inl _ => 0
--     | .inr (.mk v t) => v + summ a t

-- #reduce summ _ (list_to_alt_list [1,2,3,4])

-- def summ_on_list_eqn : summ _ (list_to_alt_list k) = List.sum k := by
--   cases k
--   rfl
--   case _ h t =>
--   simp [summ, list_to_alt_list]
--   exact summ_on_list_eqn

-- def replicate (v:T)(i): AltList T (i) :=
--   match i with
--   | .zero => .inl .unit
--   | .succ k => .inr (.mk v (replicate v k))

-- #reduce replicate 69 3


-- def PSigma_ext {P:A->Sort _}(a b:PSigma P)(c1:a.1=b.1)(c2:a.2 = cast (by rw [c1]) b.2): a = b := by
--   let (.mk v1 p1) := a
--   let (.mk v2 p2) := b
--   dsimp at c1
--   subst c1
--   dsimp at c2
--   rw [c2]

-- def natp_mono : Lean.Order.monotone (NatP) := by
--   intro A B h
--   reduce at h; reduce
--   congr


def Seqv (T : Sort _) := Stream' T

@[reducible]
def Seqv.next (s : Seqv T) : Seqv T := fun i => s (i + 1)

@[reducible]
def Seqv.get (s : Seqv T) : T := s 0

def Seqv.truncate (s : Seqv T) (n : Nat) : List T :=
  match n with
  | 0 => []
  | a + 1 => s.get :: Seqv.truncate (s.next) a

@[reducible]
def SeqvEq (a b : Seqv T) :=
  ∀ i, (iterf i (fun x => x.next) a).get = (iterf i (fun x => x.next) b).get

def iterf_next_val_eqn (s : Seqv T) (n : Nat) :
    iterf n (fun x => x.next) s = fun i => s (i + n) := by
  induction n with
  | zero =>
    funext i
    rw [Nat.add_zero]
    rfl
  | succ a ih =>
    funext i
    change (iterf a (fun x => x.next) s) (i + 1) = s (i + (a + 1))
    rw [ih]
    dsimp
    congr 1
    grind

def iterf_next_eq_eqn (s : Seqv T) (n : Nat)
: (iterf n (fun x => x.next) s).get = s n
:= by
  change iterf n (fun x => x.next) s 0 = s n
  rw [iterf_next_val_eqn s n]
  exact congrArg s (Nat.zero_add n)

def seqv_ext_eqn {a b : Seqv T} (k2 : SeqvEq a b) : a = b := by
  funext i
  have h := k2 i
  rw [iterf_next_eq_eqn a i, iterf_next_eq_eqn b i] at h
  exact h

def replicate (v : T) : Seqv T := fun _ => v

def clatz_map (n:Nat) :=
  let md := n % 2
  if md = 0 then n / 2
  else n*3 + 1

def clatz_pos_cnj :=
  ∀ n (_:n>0), ∃ i, iterf i clatz_map n = 1

def clatz_seqv (n:Nat): Seqv Nat :=
  fun i => iterf i clatz_map n

#reduce Seqv.truncate (clatz_seqv 178) 50

def as_term_seqv_part (n:Nat)(base:NumBase): Tm base × Nat :=
  let (.mk b e) := base
  let d := n / b;
  let rem := n - d * b;
  by
    refine .mk (.mk rem (?_)) d
    unfold rem d; dsimp
    rw [← @Nat.mod_eq_sub_div_mul]
    refine Nat.mod_lt n ?_
    exact Nat.zero_lt_of_lt e

def TmNumS (base:NumBase) := Seqv (Tm base)

def as_term_seqv_2 (base : NumBase) (n:Nat) : TmNumS base :=
  Stream'.corec' (as_term_seqv_part . base) n


structure AddState (base:NumBase) where
  carry : Nat
  xs : TmNumS base
  ys : TmNumS base

def add_step (base : NumBase) (st : AddState base) : (Tm base) × (AddState base) :=
  let s := st.xs.head.1 + st.ys.head.1 + st.carry
  by
    refine (.mk (s % base.1) ?_, { carry := s / base.1, xs := st.xs.tail, ys := st.ys.tail })
    refine Nat.mod_lt _ ?_
    exact Nat.zero_lt_of_lt (st.xs.head.2)


def add_tm_num (xs ys : TmNumS base) : TmNumS base :=
  Stream'.corec' (add_step base) { carry := 0, xs := xs, ys := ys }

def n_v2 := as_term_seqv_2 base_2 99

def xmpl_3 := add_tm_num n_v2 n_v2

def coefs (b:NumBase): Seqv Nat :=
  fun i => b.1 ^ i

#reduce (Stream'.zip (fun a b => a.1 * b) xmpl_3 (coefs base_2)).take 30 |>.foldl (Nat.add) 0

def add_inv_part (s:TmNumS base): TmNumS base :=
  let ot := ov_term base
  by
    refine s.map (fun i => .mk (ot - i.1) ?_)
    refine Nat.sub_lt_of_lt ?_
    refine Nat.sub_lt_right_of_lt_add ?_ ?_
    let p := base.2
    exact Nat.one_le_of_lt p
    exact lt_add_one _

def add_inv (s:TmNumS base): TmNumS base :=
  add_tm_num (as_term_seqv_2 base 1) (add_inv_part s)

def z := add_tm_num n_v2 (add_inv n_v2)
#reduce (Stream'.zip (fun a b => a.1 * b) z (coefs base_2)).take 70 |>.foldl (Nat.add) 0

def tm_zero : Tm base := .mk 0 (by grind)
def tm_num_zero_2 : TmNumS base := replicate tm_zero

def is_finite_tm_num (s:TmNumS base) :=
  (k:Nat) ×' ∀ i (_:i>=k), s i = tm_num_zero_2 i

def as_nat_repr (s:TmNumS base)(c:is_finite_tm_num s): Nat :=
  let rec loop : Nat -> Nat
    | 0 => 0
    | n + 1 => (s n).1 * (base.1 ^ n) + loop n
  loop c.1

lemma as_term_seqv_part_zero (base : NumBase) :
    as_term_seqv_part 0 base = (tm_zero, 0) := by
  unfold as_term_seqv_part tm_zero
  let (.mk _ _) := base
  simp

def nat_rat_wmap : wmap Nat Rat := by
  refine mkwmap ?_ ?_ ?_
  {
    intro n
    refine mkRat ?_ 1
    exact Int.ofNat n
  }
  {
    intro q; exact (q.1.natAbs / q.2)
  }
  intro n
  rw [Rat.num_mkRat]
  simp only [
    one_ne_zero, ↓reduceIte, Int.ofNat_eq_natCast,
    Int.natAbs_natCast, Nat.gcd_one_left,
    Nat.cast_one, EuclideanDomain.div_one
  ]
  have eqn1 : (mkRat (↑n) 1).den = 1 := by
    rw [Rat.mkRat_one]
    simp only [Int.cast_natCast, Rat.den_natCast]
  rw [eqn1]
  simp only [Nat.div_one]

-- example : hmor1 (fun i => Nat.div i 2) (fun i => Rat.div i 2) nat_rat_wmap.1.2 := by
--   intro a
--   simp [nat_rat_wmap]
--   rw [@Nat.div_eq_sub_mod_div]
--   refine Nat.eq_div_of_mul_eq_left ?_ ?_
--   exact (a.div 2).den_nz
--   rw [Nat.div_eq]
--   split
--   {
--     rw?
--   }
--   {

--   }


-- def xmpl : is_finite_tm_num n_v2 := by
--   refine .mk 7 ?_
--   intro i h
--   -- Express the arbitrary index `i` as `7 + d` since `i >= 7`
--   obtain ⟨d, rfl⟩ := Nat.exists_eq_add_of_le h

--   -- Proceed by induction on the offset `d`
--   induction d with
--   | zero =>
--     -- Base case: exactly at index 7.
--     -- Because 99 / (2^7) = 0, the stream state evaluates to 0.
--     reduce
--     rfl
--   | succ d ih =>
--     -- Inductive step: if the state at 7 + d is 0, the next state is also 0.
--     -- Unfold the sequence generation and apply our zero lemma.
--     unfold n_v2 as_term_seqv_2
--     rw [Stream'.corec'_eq]
--     reduce
--     congr
--     simp only [Nat.add_eq, zero_add, shift_tr_fun_g, Nat.sub_eq]
--     generalize Stream'.iterate (fun x => x.div 2) 49 (7 + d) = j
--     refine Eq.symm (Nat.eq_sub_of_add_eq' ?_)
--     simp only [add_zero]
--     have eqn1 : j.div 2 = j / 2 := rfl
--     rw [eqn1]
--     rw [← Nat.mul_two]

--     admit

-- #reduce

-- axiom mu (np:Nonempty A)(f:A->A)[Preorder A](m:Monotone f): A -> A
-- axiom mu_def_eqn (x:Nonempty A)(f:A->A)[Preorder A](m:Monotone f): mu x f m = fun i => f (mu x f m i)

-- theorem false_of_mu : False := by
--   -- 1. Choose A to be the Integers, which is a nonempty preorder
--   have np : Nonempty Int := ⟨0⟩

--   -- 2. Define a monotone function with no fixed point: f(x) = x + 1
--   let f : Int → Int := fun x => x + 1
--   have m : Monotone f := fun x y h => by
--     dsimp [f]
--     omega

--   -- 3. Apply the fixed-point axiom equation to our function
--   have h_eq := mu_def_eqn np f m

--   -- 4. Apply both sides of the function equality to an arbitrary input (like 0)
--   have h_zero := congrFun h_eq 0

--   -- 5. Simplify f(X) to X + 1, leaving us with X = X + 1
--   dsimp [f] at h_zero

--   -- 6. Let omega handle the integer contradiction (X = X + 1 is impossible)
--   omega


def there_must_not_be_another_path : (∃ (p: path v v), p ≠ id_path v) → False := by
  rintro ⟨p, hp⟩
  apply hp
  funext P x
  classical
  let f : (T : Sort _) → T → T := fun T x ↦
    if h : T = P v then
      cast h.symm (p P (cast h x))
    else
      x
  have hf := parametricity f
  have hx := congrFun (congrFun hf (P v)) x
  simpa [f] using hx


theorem eq_is_refl {a b:A}(e: Eq a b):
  e = (Eq.casesOn (motive := fun a_1 t => b = a_1 → e ≍ t → a = b) e
      (fun h =>
        Eq.ndrec (motive := fun {b} => ∀ (e : a = b), e ≍ Eq.refl a → a = b) (fun _ _ => Eq.refl a) (Eq.symm h) e)
      (Eq.refl b) (HEq.refl e)) := by cases e; rfl


theorem eq_uniq: ∀ (p q: a = b), p = q :=
  fun p q => Eq.subst (eq_is_refl p) (Eq.subst (eq_is_refl q) (Eq.refl _))
