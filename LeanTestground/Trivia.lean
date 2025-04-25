import LeanTestground.Basic

def mod2_weq : wmap Bool Nat := by
  refine mkwmap ?_ ?_ ?_
  exact fun i => if i then 1 else 0
  exact fun i => i % 2 != 0
  simp

def mod2 : quo (fun (i:Bool) => if i then 1 else 0) := by
  unfold quo
  intro i
  refine Subtype.mk (if i % 2 == 0 then false else true) ?_
  dsimp
  induction i
  dsimp
  case _ k ih =>
  generalize (k % 2 == 0) = l2 at ih
  cases l2
  {
    dsimp at ih
    -- let eq1 : k + 1 % 2 = 0 := by
    --   rw [<-ih]
    --   dsimp
    rw [<-ih]
    dsimp
    let x1 := transp mod2_weq
    unfold mod2_weq mkwmap at x1
    simp at x1
    let _ := x1 true
    admit
  }
  {
    dsimp at ih
    rw [<-ih]
    dsimp
  }

  -- refine Eq.symm (Nat.le_antisymm ?_ ?_)
  -- generalize ((k+1)%2 == 0) = l
  -- cases l
  -- dsimp

