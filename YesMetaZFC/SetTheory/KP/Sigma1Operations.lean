import YesMetaZFC.SetTheory.KP.Sigma1

/-! # Σ₁ 正规形的复合与集合像

每个存在见证都有实际集合界；后续 J 递归直接消费这些正规形。
-/

namespace YesMetaZFC.SetTheory.Definitional.Project
universe u
variable {M : Structure.{u}}

def S1_binary.comp {n} (φ ψ : S1_binary n) : S1_binary n where
  matrix := {
    body := Formula.existsMem .newest (Formula.existsMem (.bound 1) (Formula.existsMem (.bound 2)
      (.conj (φ.matrix_m (fun i => .bound ⟨i.val + 6, by omega⟩) (.bound 5) (.bound 2) (.bound 1))
        (ψ.matrix_m (fun i => .bound ⟨i.val + 6, by omega⟩) (.bound 2) (.bound 4) .newest))))
    freeClosed := by simp -implicitDefEqProofs [Definitional.Formula.FreeClosed]
    delta0 := .existsMem _ (.existsMem _ (.existsMem _
      (.conj (φ.matrix.delta0.bind_l _) (ψ.matrix.delta0.bind_l _)))) }

theorem S1_binary.comp_sat_l (hKP : M.Models KP) {n} (φ ψ : S1_binary n) (ρ : Env M n) (x y : M.Domain) :
    (φ.comp ψ).schema.denote ρ x y ↔ ∃ z, φ.schema.denote ρ x z ∧ ψ.schema.denote ρ z y := by
  rw [S1_binary.sat_l]
  simp only [S1_binary.comp, Formula.satisfies_existsMem_iff, Formula.satisfies_conj_iff, S1_binary.matrix_sat_l]
  change (∃ T z, M.mem z T ∧ ∃ w, M.mem w T ∧ ∃ v, M.mem v T ∧
    φ.matrix_binary.toBinarySchema.denote (ρ.push x) z w ∧ ψ.matrix_binary.toBinarySchema.denote (ρ.push z) y v) ↔ _
  constructor
  · rintro ⟨_, z, _, w, _, v, _, hw, hv⟩
    exact ⟨z, (φ.sat_l ρ x z).mpr ⟨w, hw⟩, (ψ.sat_l ρ z y).mpr ⟨v, hv⟩⟩
  · rintro ⟨z, hz, hy⟩
    obtain ⟨w, hw⟩ := (φ.sat_l ρ x z).mp hz
    obtain ⟨v, hv⟩ := (ψ.sat_l ρ z y).mp hy
    obtain ⟨P, hp⟩ := KP.exists_pair hKP z w
    obtain ⟨T, ht⟩ := KP.exists_insert hKP P v
    exact ⟨T, z, (ht z).mpr (Or.inl ((hp z).mpr (Or.inl rfl))), w,
      (ht w).mpr (Or.inl ((hp w).mpr (Or.inr rfl))), v, (ht v).mpr (Or.inr rfl), hw, hv⟩

def S1_binary.image {n} (φ : S1_binary n) : S1_binary n where
  matrix := {
    body := .conj
      (Formula.forallMem (.bound 2) (Formula.existsMem (.bound 2) (Formula.existsMem (.bound 2)
        (φ.matrix_m (fun i => .bound ⟨i.val + 6, by omega⟩) (.bound 2) (.bound 1) .newest))))
      (Formula.forallMem (.bound 1) (Formula.existsMem (.bound 3) (Formula.existsMem (.bound 2)
        (φ.matrix_m (fun i => .bound ⟨i.val + 6, by omega⟩) (.bound 1) (.bound 2) .newest))))
    freeClosed := by simp -implicitDefEqProofs [Definitional.Formula.FreeClosed]
    delta0 := .conj (.forallMem _ (.existsMem _ (.existsMem _ (φ.matrix.delta0.bind_l _))))
      (.forallMem _ (.existsMem _ (.existsMem _ (φ.matrix.delta0.bind_l _)))) }

theorem S1_binary.image_sat_l (hKP : M.Models KP) {n} (φ : S1_binary n) (ρ : Env M n) (X Y : M.Domain)
    (ht : ∀ x, M.mem x X → ∃ y, φ.schema.denote ρ x y)
    (hu : ∀ x, M.mem x X → ∀ y z, φ.schema.denote ρ x y → φ.schema.denote ρ x z → y = z) :
    φ.image.schema.denote ρ X Y ↔ ∀ y, M.mem y Y ↔ ∃ x, M.mem x X ∧ φ.schema.denote ρ x y := by
  rw [S1_binary.sat_l]
  simp only [S1_binary.image, Formula.satisfies_conj_iff, Formula.satisfies_forallMem_iff,
    Formula.satisfies_existsMem_iff, S1_binary.matrix_sat_l]
  change (∃ T, (∀ x, M.mem x X → ∃ y, M.mem y Y ∧ ∃ w, M.mem w T ∧
    φ.matrix_binary.toBinarySchema.denote (ρ.push x) y w) ∧
    (∀ y, M.mem y Y → ∃ x, M.mem x X ∧ ∃ w, M.mem w T ∧
      φ.matrix_binary.toBinarySchema.denote (ρ.push x) y w)) ↔ _
  constructor
  · rintro ⟨T, ht, hy⟩ y
    constructor
    · intro h
      obtain ⟨x, hx, w, _, hw⟩ := hy y h
      exact ⟨x, hx, (φ.sat_l ρ x y).mpr ⟨w, hw⟩⟩
    · rintro ⟨x, hx, hxy⟩
      obtain ⟨z, hz, w, _, hw⟩ := ht x hx
      exact (hu x hx z y ((φ.sat_l ρ x z).mpr ⟨w, hw⟩) hxy) ▸ hz
  · intro hy
    obtain ⟨T, hT⟩ := KP.s1_collection_l hKP φ ρ X ht
    refine ⟨T, fun x hx => ?_, fun y hyY => ?_⟩
    · obtain ⟨y, _, w, hwT, hw⟩ := hT x hx
      exact ⟨y, (hy y).mpr ⟨x, hx, (φ.sat_l ρ x y).mpr ⟨w, hw⟩⟩, w, hwT, hw⟩
    · obtain ⟨x, hx, hxy⟩ := (hy y).mp hyY
      obtain ⟨z, _, w, hwT, hw⟩ := hT x hx
      have he := hu x hx z y ((φ.sat_l ρ x z).mpr ⟨w, hw⟩) hxy
      subst z
      exact ⟨x, hx, w, hwT, hw⟩

/-- 互补 Σ₁ 条件的精确分离图；单个证书同时界住所有成员的正反见证。 -/
def S1_binary.separate {n} (φ ψ : Delta0BinarySchema n) : S1_binary n where
  matrix := {
    body := .conj (Formula.subset (.bound 1) (.bound 2)) (Formula.forallMem (.bound 2)
      (.disj (.conj (.mem .newest (.bound 2)) (Formula.existsMem (.bound 1)
        (binary_pred_m φ.toBinarySchema (fun i => .bound ⟨i.val + 5, by omega⟩) (.bound 1) .newest)))
        (.conj (.neg (.mem .newest (.bound 2))) (Formula.existsMem (.bound 1)
          (binary_pred_m ψ.toBinarySchema (fun i => .bound ⟨i.val + 5, by omega⟩) (.bound 1) .newest)))))
    freeClosed := by simp -implicitDefEqProofs [Definitional.Formula.FreeClosed]
    delta0 := .conj (.atom _ _ _) (.forallMem _ (.disj
      (.conj (.mem _ _) (.existsMem _ (φ.delta0.bind_l _)))
      (.conj (.neg (.mem _ _)) (.existsMem _ (ψ.delta0.bind_l _))))) }

theorem S1_binary.separate_sat_l (hKP : M.Models KP) {n} (φ ψ : Delta0BinarySchema n) (ρ : Env M n) (X Y : M.Domain)
    (hc : ∀ x, M.mem x X → ((∃ w, φ.toBinarySchema.denote ρ x w) ↔ ¬ ∃ w, ψ.toBinarySchema.denote ρ x w)) :
    (S1_binary.separate φ ψ).schema.denote ρ X Y ↔
      ∀ x, M.mem x Y ↔ M.mem x X ∧ ∃ w, φ.toBinarySchema.denote ρ x w := by
  rw [S1_binary.sat_l]
  simp only [S1_binary.separate, Formula.satisfies_conj_iff, Formula.satisfies_subset_iff,
    Formula.satisfies_forallMem_iff, Formula.satisfies_disj_iff, Formula.satisfies_mem_iff,
    Formula.satisfies_neg_iff, Formula.satisfies_existsMem_iff, binary_pred_sat_l]
  change (∃ T, M.MemberSubset Y X ∧ ∀ x, M.mem x X →
    (M.mem x Y ∧ ∃ w, M.mem w T ∧ φ.toBinarySchema.denote ρ x w) ∨
      (¬ M.mem x Y ∧ ∃ w, M.mem w T ∧ ψ.toBinarySchema.denote ρ x w)) ↔ _
  constructor
  · rintro ⟨T, hs, h⟩ x
    constructor
    · intro hx
      exact ⟨hs x hx, ((h x (hs x hx)).elim (fun h => h.2.imp (fun _ h => h.2)) (fun h => (h.1 hx).elim))⟩
    · rintro ⟨hx, w, hw⟩
      exact ((h x hx).elim And.left (fun h => ((hc x hx).mp ⟨w, hw⟩ (h.2.imp (fun _ h => h.2))).elim))
  · intro hy
    let θ : Delta0BinarySchema n := {
      body := .disj φ.body ψ.body
      freeClosed := by simpa only [Definitional.Formula.FreeClosed] using And.intro φ.freeClosed ψ.freeClosed
      delta0 := .disj φ.delta0 ψ.delta0 }
    have hθ x w : θ.toBinarySchema.denote ρ x w ↔ φ.toBinarySchema.denote ρ x w ∨ ψ.toBinarySchema.denote ρ x w :=
      Formula.satisfies_disj_iff _ _ _
    obtain ⟨T, ht⟩ := KP.collection_exists_d hKP θ ρ X (by
      intro x hx
      classical
      by_cases hp : ∃ w, φ.toBinarySchema.denote ρ x w
      · exact hp.imp (fun w hw => (hθ x w).mpr (Or.inl hw))
      · have hn : ∃ w, ψ.toBinarySchema.denote ρ x w := Classical.not_not.mp (fun hn => hp ((hc x hx).mpr hn))
        exact hn.imp (fun w hw => (hθ x w).mpr (Or.inr hw)))
    refine ⟨T, fun x hx => ((hy x).mp hx).1, fun x hx => ?_⟩
    obtain ⟨w, hw, h⟩ := ht x hx
    rcases (hθ x w).mp h with h | h
    · exact Or.inl ⟨(hy x).mpr ⟨hx, w, h⟩, w, hw, h⟩
    · exact Or.inr ⟨fun hxy => (hc x hx).mp ((hy x).mp hxy).2 ⟨w, h⟩, w, hw, h⟩

end YesMetaZFC.SetTheory.Definitional.Project
