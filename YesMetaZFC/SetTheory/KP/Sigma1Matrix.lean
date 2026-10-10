import YesMetaZFC.SetTheory.KP.Sigma1Operations

/-! # Σ₁ 组合子的见证矩阵

这里显式保留每层证书的集合界，供非可容许层中的局部见证装配与读取使用。
这些等价只展开实际正规形，不假定层内存在收集。
-/

namespace YesMetaZFC.SetTheory.Definitional.Project
universe u
variable {M : Structure.{u}}

theorem S1_binary.comp_matrix_l {n} (φ ψ : S1_binary n) (ρ : Env M n) (x y B : M.Domain) :
    Formula.satisfies (((ρ.push x).push y).push B) (φ.comp ψ).matrix.body ↔
      ∃ z, M.mem z B ∧ ∃ w, M.mem w B ∧ ∃ v, M.mem v B ∧
        Formula.satisfies (((ρ.push x).push z).push w) φ.matrix.body ∧
        Formula.satisfies (((ρ.push z).push y).push v) ψ.matrix.body := by
  simp only [S1_binary.comp, Formula.satisfies_existsMem_iff, Formula.satisfies_conj_iff, S1_binary.matrix_sat_l]
  rfl

theorem S1_binary.image_matrix_l {n} (φ : S1_binary n) (ρ : Env M n) (X Y B : M.Domain) :
    Formula.satisfies (((ρ.push X).push Y).push B) φ.image.matrix.body ↔
      (∀ x, M.mem x X → ∃ y, M.mem y Y ∧ ∃ w, M.mem w B ∧
        Formula.satisfies (((ρ.push x).push y).push w) φ.matrix.body) ∧
      (∀ y, M.mem y Y → ∃ x, M.mem x X ∧ ∃ w, M.mem w B ∧
        Formula.satisfies (((ρ.push x).push y).push w) φ.matrix.body) := by
  simp only [S1_binary.image, Formula.satisfies_conj_iff, Formula.satisfies_forallMem_iff,
    Formula.satisfies_existsMem_iff, S1_binary.matrix_sat_l]
  rfl

theorem S1_binary.image_mono_l {n} (φ : S1_binary n) (ρ : Env M n) {X Y B T : M.Domain}
    (h : Formula.satisfies (((ρ.push X).push Y).push B) φ.image.matrix.body) (hb : M.MemberSubset B T) :
    Formula.satisfies (((ρ.push X).push Y).push T) φ.image.matrix.body := by
  obtain ⟨h, g⟩ := (φ.image_matrix_l ρ X Y B).mp h
  exact (φ.image_matrix_l ρ X Y T).mpr
    ⟨fun x hx => (h x hx).imp (fun y hy => ⟨hy.1, hy.2.imp (fun w hw => ⟨hb w hw.1, hw.2⟩)⟩),
      fun y hy => (g y hy).imp (fun x hx => ⟨hx.1, hx.2.imp (fun w hw => ⟨hb w hw.1, hw.2⟩)⟩)⟩

theorem S1_binary.pair_matrix_l (hE : Extensional M) {n} (φ ψ : S1_binary n) (ρ : Env M n) (x p B : M.Domain) :
    Formula.satisfies (((ρ.push x).push p).push B) (φ.pair ψ).matrix.body ↔
      ∃ a, M.mem a B ∧ ∃ b, M.mem b B ∧ ∃ w, M.mem w B ∧ ∃ v, M.mem v B ∧
        Formula.satisfies (((ρ.push x).push a).push w) φ.matrix.body ∧
        Formula.satisfies (((ρ.push x).push b).push v) ψ.matrix.body ∧ KPair_d M p a b := by
  simp only [S1_binary.pair, Formula.satisfies_existsMem_iff, Formula.satisfies_conj_iff,
    S1_binary.matrix_sat_l, kpair0_sat_l hE]
  rfl

theorem S1_binary.of_delta0_matrix_l {n} (φ : Delta0BinarySchema n) (ρ : Env M n) (x y B : M.Domain) :
    Formula.satisfies (((ρ.push x).push y).push B) (S1_binary.of_delta0 φ).matrix.body ↔ φ.toBinarySchema.denote ρ x y := by
  change Formula.satisfies (((ρ.push x).push y).push B) φ.body.weaken ↔ _
  rw [Definitional.Formula.weaken, Formula.satisfies_rename]
  rfl

/-- 在给定输入集及见证界内查询输出；参数槽为 B、X、原参数。 -/
def S1_binary.bounded_image_s {n} (φ : S1_binary n) : Delta0UnarySchema (n + 2) where
  body := Formula.existsMem (.bound 2) (Formula.existsMem (.bound 2)
    (φ.matrix_m (fun i => .bound ⟨i.val + 5, by omega⟩) (.bound 1) (.bound 2) .newest))
  freeClosed := by simp -implicitDefEqProofs
  delta0 := .existsMem _ (.existsMem _ (φ.matrix.delta0.bind_l _))
theorem S1_binary.bounded_image_sat_l {n} (φ : S1_binary n) (ρ : Env M n) (B X y : M.Domain) :
    φ.bounded_image_s.toUnarySchema.denote ((ρ.push X).push B) y ↔
      ∃ x, M.mem x X ∧ ∃ w, M.mem w B ∧ Formula.satisfies (((ρ.push x).push y).push w) φ.matrix.body := by
  simp only [UnarySchema.denote, S1_binary.bounded_image_s, Formula.satisfies_existsMem_iff, S1_binary.matrix_sat_l]
  rfl

end YesMetaZFC.SetTheory.Definitional.Project
