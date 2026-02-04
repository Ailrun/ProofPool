def MyInt' : Type := Nat × Nat

def MyInt.eq (n k : MyInt') : Prop :=
  n.1 + k.2 = n.2 + k.1

def MyInt.eq.eqv : Equivalence MyInt.eq where
  refl := by unfold eq; intros; omega
  symm := by unfold eq; intros; omega
  trans := by unfold eq; intros; omega

instance : Setoid MyInt' where
  r := MyInt.eq
  iseqv := MyInt.eq.eqv

def MyInt := Quotient instSetoidMyInt'

def MyInt.mk (n : MyInt') : MyInt := Quotient.mk _ n

instance : OfNat MyInt n where
  ofNat := MyInt.mk (n, 0)

def MyInt.neg' (n : MyInt') : MyInt := .mk (n.2, n.1)

instance : Neg MyInt where
  neg (n : MyInt) := n.lift MyInt.neg' <| by
    intro (a₁, a₂) (a'₁, a'₂) heq
    apply Quotient.sound
    simp only [· ≈ ·, Setoid.r, MyInt.eq] at *
    omega

def MyInt.add' (n k : MyInt') : MyInt := .mk (n.1 + k.1, n.2 + k.2)

instance : Add MyInt where
  add (n : MyInt) := n.lift₂ MyInt.add' <| by
    intro (a₁, a₂) (b₁, b₂) (a'₁, a'₂) (b'₁, b'₂) heq heq'
    apply Quotient.sound
    simp_all only [· ≈ ·, Setoid.r, MyInt.eq]
    omega

def MyInt.mul' (n k : MyInt') : MyInt := .mk (n.1 * k.1 + n.2 * k.2, n.1 * k.2 + n.2 * k.1)

instance : Mul MyInt where
  mul (n : MyInt) := n.lift₂ MyInt.mul' <| by
    intro (a₁, a₂) (b₁, b₂) (a'₁, a'₂) (b'₁, b'₂) heq heq'
    calc MyInt.mul' (a₁, a₂) (b₁, b₂)
      _ = MyInt.mul' (a'₁, a'₂) (b₁, b₂)   := by
        apply Quotient.sound
        simp_all only [· ≈ ·, Setoid.r, MyInt.eq]
        calc a₁ * b₁ + a₂ * b₂ + (a'₁ * b₂ + a'₂ * b₁)
          _ = (a₁ + a'₂) * b₁ + (a₂ + a'₁) * b₂         := by lia
          _ = (a₂ + a'₁) * b₁ + (a₁ + a'₂) * b₂         := by simp_all
          _ = a₁ * b₂ + a₂ * b₁ + (a'₁ * b₁ + a'₂ * b₂) := by lia
      _ = MyInt.mul' (a'₁, a'₂) (b'₁, b'₂) := by
        apply Quotient.sound
        simp_all only [· ≈ ·, Setoid.r, MyInt.eq]
        calc a'₁ * b₁ + a'₂ * b₂ + (a'₁ * b'₂ + a'₂ * b'₁)
          _ = a'₁ * (b₁ + b'₂) + a'₂ * (b₂ + b'₁)           := by lia
          _ = a'₁ * (b₂ + b'₁) + a'₂ * (b₁ + b'₂)           := by simp_all
          _ = a'₁ * b₂ + a'₂ * b₁ + (a'₁ * b'₁ + a'₂ * b'₂) := by lia

def MyInt.sub' (n k : MyInt') : MyInt := .mk (n.1 + k.2, n.2 + k.1)

instance : Sub MyInt where
  sub (n : MyInt) := n.lift₂ MyInt.sub' <| by
    intro (a₁, a₂) (b₁, b₂) (a'₁, a'₂) (b'₁, b'₂) heq heq'
    apply Quotient.sound
    simp_all only [· ≈ ·, Setoid.r, MyInt.eq]
    omega
