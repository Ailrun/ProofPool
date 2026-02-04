def MyZ' : Type := Nat × Nat

def MyZ.eq (n k : MyZ') : Prop :=
  n.1 + k.2 = n.2 + k.1

def MyZ.eq.eqv : Equivalence MyZ.eq where
  refl := by unfold eq; intros; omega
  symm := by unfold eq; intros; omega
  trans := by unfold eq; intros; omega

instance : Setoid MyZ' where
  r := MyZ.eq
  iseqv := MyZ.eq.eqv

def MyZ := Quotient instSetoidMyZ'

def MyZ.mk (n : MyZ') : MyZ := Quotient.mk _ n

instance : OfNat MyZ n where
  ofNat := MyZ.mk (n, 0)

def MyZ.neg' (n : MyZ') : MyZ := .mk (n.2, n.1)

instance : Neg MyZ where
  neg (n : MyZ) := n.lift MyZ.neg' <| by
    intro (a₁, a₂) (a'₁, a'₂) heq
    apply Quotient.sound
    simp only [· ≈ ·, Setoid.r, MyZ.eq] at *
    omega

def MyZ.add' (n m : MyZ') : MyZ := .mk (n.1 + m.1, n.2 + m.2)

instance : Add MyZ where
  add (n : MyZ) := n.lift₂ MyZ.add' <| by
    intro (a₁, a₂) (b₁, b₂) (a'₁, a'₂) (b'₁, b'₂) heq heq'
    apply Quotient.sound
    simp only [· ≈ ·, Setoid.r, MyZ.eq] at *
    omega

instance : Std.Commutative instAddMyZ.1 where
  comm (n m : MyZ) := by
    cases n using Quotient.ind; cases m using Quotient.ind
    apply Quotient.sound
    simp only [· ≈ ·, Setoid.r, MyZ.eq] at *
    omega

instance : Std.Associative instAddMyZ.1 where
  assoc (n m k : MyZ) := by
    cases n using Quotient.ind; cases m using Quotient.ind; cases k using Quotient.ind
    apply Quotient.sound
    simp only [· ≈ ·, Setoid.r, MyZ.eq] at *
    omega

def MyZ.mul' (n m : MyZ') : MyZ := .mk (n.1 * m.1 + n.2 * m.2, n.1 * m.2 + n.2 * m.1)

instance : Mul MyZ where
  mul (n : MyZ) := n.lift₂ MyZ.mul' <| by
    intro (a₁, a₂) (b₁, b₂) (a'₁, a'₂) (b'₁, b'₂) heq heq'
    calc MyZ.mul' (a₁, a₂) (b₁, b₂)
      _ = MyZ.mul' (a'₁, a'₂) (b₁, b₂)   := by
        apply Quotient.sound
        simp only [· ≈ ·, Setoid.r, MyZ.eq] at *
        calc a₁ * b₁ + a₂ * b₂ + (a'₁ * b₂ + a'₂ * b₁)
          _ = (a₁ + a'₂) * b₁ + (a₂ + a'₁) * b₂         := by lia
          _ = (a₂ + a'₁) * b₁ + (a₁ + a'₂) * b₂         := by simp_all
          _ = a₁ * b₂ + a₂ * b₁ + (a'₁ * b₁ + a'₂ * b₂) := by lia
      _ = MyZ.mul' (a'₁, a'₂) (b'₁, b'₂) := by
        apply Quotient.sound
        simp only [· ≈ ·, Setoid.r, MyZ.eq] at *
        calc a'₁ * b₁ + a'₂ * b₂ + (a'₁ * b'₂ + a'₂ * b'₁)
          _ = a'₁ * (b₁ + b'₂) + a'₂ * (b₂ + b'₁)           := by lia
          _ = a'₁ * (b₂ + b'₁) + a'₂ * (b₁ + b'₂)           := by simp_all
          _ = a'₁ * b₂ + a'₂ * b₁ + (a'₁ * b'₁ + a'₂ * b'₂) := by lia

instance : Std.Commutative instMulMyZ.1 where
  comm (n m : MyZ) := by
    cases n using Quotient.ind; cases m using Quotient.ind
    apply Quotient.sound
    simp only [· ≈ ·, Setoid.r, MyZ.eq] at *
    lia

instance : Std.Associative instMulMyZ.1 where
  assoc (n m k : MyZ) := by
    cases n using Quotient.ind; cases m using Quotient.ind; cases k using Quotient.ind
    apply Quotient.sound
    simp only [· ≈ ·, Setoid.r, MyZ.eq] at *
    lia

def MyZ.sub' (n m : MyZ') : MyZ := .mk (n.1 + m.2, n.2 + m.1)

instance : Sub MyZ where
  sub (n : MyZ) := n.lift₂ MyZ.sub' <| by
    intro (a₁, a₂) (b₁, b₂) (a'₁, a'₂) (b'₁, b'₂) heq heq'
    apply Quotient.sound
    simp only [· ≈ ·, Setoid.r, MyZ.eq] at *
    omega

#check ((by apply Quotient.sound; rfl) : instSubMyZ.1 (.mk (2, 5)) (.mk (3, 10)) = 4)
