import YesMetaZFC.SetTheory.Collection
import YesMetaZFC.SetTheory.Separation
import YesMetaZFC.SetTheory.SetConstruction
import YesMetaZFC.SetTheory.Definitional.Project.Hierarchy.Substitution
import YesMetaZFC.SetTheory.Definitional.Project.Predicate

/-! # KP 中的 Σ₁ 收集与 Δ₁ 分离

矩阵始终携带实际 Δ₀ 证书。Σ₁ 关系以一个存在见证的正规形呈现；收集同时
界住输出和见证，不假定模型外部良基，也不使用全分离、幂集或选择。
-/

namespace YesMetaZFC.SetTheory
open Definitional.Project
universe u
variable {M : Structure.{u}}

namespace Definitional.Project

/-- 矩阵的槽位依次是见证、输出、输入、其余参数。 -/
structure S1_binary (n : Nat) where
  matrix : Delta0UnarySchema (n + 2)

def S1_binary.matrix_binary {n} (φ : S1_binary n) : Delta0BinarySchema (n + 1) where
  body := φ.matrix.body
  freeClosed := φ.matrix.freeClosed
  delta0 := φ.matrix.delta0

def S1_binary.schema {n} (φ : S1_binary n) : BinarySchema n where
  body := .existsE φ.matrix.body
  freeClosed := by simpa only [Definitional.Formula.FreeClosed] using φ.matrix.freeClosed

theorem S1_binary.sat_l {n} (φ : S1_binary n) (ρ : Env M n) (x y : M.Domain) :
    φ.schema.denote ρ x y ↔ ∃ w, Formula.satisfies (((ρ.push x).push y).push w) φ.matrix.body := by
  simp only [S1_binary.schema, BinarySchema.denote, Formula.satisfies_exists_iff]

def S1_binary.matrix_m {n d} (φ : S1_binary n) (e : Fin n → Term d) (x y w : Term d) : Formula 1 d :=
  binary_pred_m φ.matrix_binary.toBinarySchema (Fin.cases x e) y w

@[simp] theorem S1_binary.matrix_closed_l {n d} (φ : S1_binary n) (e : Fin n → Term d) (x y w : Term d)
    (he : ∀ i, (e i).freeSupport = []) (hx : x.freeSupport = []) (hy : y.freeSupport = [])
    (hw : w.freeSupport = []) : (φ.matrix_m e x y w).FreeClosed :=
  binary_pred_closed_l _ _ _ _ (Fin.cases hx he) hy hw

theorem S1_binary.matrix_sat_l {n d} (φ : S1_binary n) (η : Env M d) (e : Fin n → Term d) (x y w : Term d) :
    Formula.satisfies η (φ.matrix_m e x y w) ↔
      φ.matrix_binary.toBinarySchema.denote
        ((⟨fun i => (e i).eval η, η.free⟩ : Env M n).push (x.eval η)) (y.eval η) (w.eval η) := by
  rw [S1_binary.matrix_m, binary_pred_sat_l]
  have he : (⟨fun i => (Fin.cases x e i : Term d).eval η, η.free⟩ : Env M (n+1)) =
      (⟨fun i => (e i).eval η, η.free⟩ : Env M n).push (x.eval η) := by
    rw [Env.mk.injEq]
    exact ⟨funext (Fin.cases rfl (fun _ => rfl)), rfl⟩
  rw [he]

/-- 每条 Δ₀ 关系都有实际 Σ₁ 表示；见证槽仅作存在量化。 -/
def S1_binary.of_delta0 {n} (φ : Delta0BinarySchema n) : S1_binary n where
  matrix := {
    body := φ.body.weaken
    freeClosed := by simpa only [Definitional.Formula.freeClosed_weaken] using φ.freeClosed
    delta0 := φ.delta0.rename_l Fin.succ }

theorem S1_binary.of_delta0_sat_l {n} (φ : Delta0BinarySchema n) (ρ : Env M n) (x y : M.Domain) :
    (S1_binary.of_delta0 φ).schema.denote ρ x y ↔ φ.toBinarySchema.denote ρ x y := by
  rw [S1_binary.sat_l]
  have hw (w : M.Domain) : Formula.satisfies (((ρ.push x).push y).push w) φ.body.weaken ↔
      φ.toBinarySchema.denote ρ x y := by
    rw [Definitional.Formula.weaken, Formula.satisfies_rename]
    rfl
  exact ⟨fun ⟨w, h⟩ => (hw w).mp h, fun h => ⟨x, (hw x).mpr h⟩⟩

end Definitional.Project

namespace KP

/-- 单次 Δ₀ 收集即可同时收集 Σ₁ 输出及其见证。 -/
theorem s1_collection_l (hKP : M.Models KP) {n} (φ : S1_binary n) (ρ : Env M n) (X : M.Domain)
    (ht : ∀ x, M.mem x X → ∃ y, φ.schema.denote ρ x y) :
    ∃ B, ∀ x, M.mem x X → ∃ y, M.mem y B ∧ ∃ w, M.mem w B ∧
      Formula.satisfies (((ρ.push x).push y).push w) φ.matrix.body := by
  let e : Fin (n + 3) → Fin (n + 4) := Fin.cases 0 (Fin.cases 1 (fun i => ⟨i.val + 3, by omega⟩))
  let ψ : Delta0BinarySchema n := {
    body := Formula.existsMem .newest (Formula.existsMem (.bound 1) (φ.matrix.body.rename e))
    freeClosed := by simp -implicitDefEqProofs [φ.matrix.freeClosed]
    delta0 := .existsMem _ (.existsMem _ (φ.matrix.delta0.rename_l e)) }
  have he x v y w : ((((ρ.push x).push v).push y).push w).reindex e =
      ((ρ.push x).push y).push w := by
    rw [Env.mk.injEq]
    exact ⟨funext (Fin.cases rfl (Fin.cases rfl (fun _ => rfl))), rfl⟩
  have hψ x v : ψ.toBinarySchema.denote ρ x v ↔ ∃ y, M.mem y v ∧ ∃ w, M.mem w v ∧
      Formula.satisfies (((ρ.push x).push y).push w) φ.matrix.body := by
    simp only [BinarySchema.denote, ψ, Formula.satisfies_existsMem_iff, Formula.satisfies_rename, he]
    rfl
  obtain ⟨C, hC⟩ := collection_exists_d hKP ψ ρ X (by
    intro x hx
    obtain ⟨y, hy⟩ := ht x hx
    obtain ⟨w, hw⟩ := (φ.sat_l ρ x y).mp hy
    obtain ⟨v, hv⟩ := exists_pair hKP y w
    exact ⟨v, (hψ x v).mpr ⟨y, (hv y).mpr (Or.inl rfl), w, (hv w).mpr (Or.inr rfl), hw⟩⟩)
  obtain ⟨B, hB⟩ := exists_union hKP C
  refine ⟨B, fun x hx => ?_⟩
  obtain ⟨v, hv, hvψ⟩ := hC x hx
  obtain ⟨y, hyv, w, hwv, hw⟩ := (hψ x v).mp hvψ
  exact ⟨y, (hB y).mpr ⟨v, hv, hyv⟩, w, (hB w).mpr ⟨v, hv, hwv⟩, hw⟩

/-- 互补的两条 Σ₁ 定义在任意集合上给出实际分离集。 -/
theorem d1_separation_l (hKP : M.Models KP) {n} (φ ψ : Delta0BinarySchema n)
    (ρ : Env M n) (X : M.Domain)
    (hc : ∀ x, M.mem x X → ((∃ w, φ.toBinarySchema.denote ρ x w) ↔
      ¬ ∃ w, ψ.toBinarySchema.denote ρ x w)) :
    ∃ Y, ∀ x, M.mem x Y ↔ M.mem x X ∧ ∃ w, φ.toBinarySchema.denote ρ x w := by
  classical
  let θ : Delta0BinarySchema n := {
    body := .disj φ.body ψ.body
    freeClosed := by simpa only [Definitional.Formula.FreeClosed] using And.intro φ.freeClosed ψ.freeClosed
    delta0 := .disj φ.delta0 ψ.delta0 }
  have ht x w : θ.toBinarySchema.denote ρ x w ↔
      φ.toBinarySchema.denote ρ x w ∨ ψ.toBinarySchema.denote ρ x w := by
    simp only [BinarySchema.denote, θ, Formula.satisfies_disj_iff]
  obtain ⟨B, hB⟩ := collection_exists_d hKP θ ρ X (by
    intro x hx
    by_cases h : ∃ w, φ.toBinarySchema.denote ρ x w
    · exact h.elim fun w hw => ⟨w, (ht x w).mpr (Or.inl hw)⟩
    · obtain ⟨w, hw⟩ := Classical.not_not.mp (fun hn => h ((hc x hx).mpr hn))
      exact ⟨w, (ht x w).mpr (Or.inr hw)⟩)
  let e : Fin (n + 2) → Fin (n + 3) := Fin.cases 0 (Fin.cases 1 (fun i => ⟨i.val + 3, by omega⟩))
  let δ : Delta0UnarySchema (n + 1) := {
    body := Formula.existsMem (.bound 1) (φ.body.rename e)
    freeClosed := by simp -implicitDefEqProofs [φ.freeClosed]
    delta0 := .existsMem _ (φ.delta0.rename_l e) }
  have he x w : (((ρ.push B).push x).push w).reindex e = (ρ.push x).push w := by
    rw [Env.mk.injEq]
    exact ⟨funext (Fin.cases rfl (Fin.cases rfl (fun _ => rfl))), rfl⟩
  have hδ x : δ.toUnarySchema.denote (ρ.push B) x ↔
      ∃ w, M.mem w B ∧ φ.toBinarySchema.denote ρ x w := by
    simp only [UnarySchema.denote, δ, Formula.satisfies_existsMem_iff, Formula.satisfies_rename, he]
    rfl
  obtain ⟨Y, hY⟩ := separation_exists_d hKP δ (ρ.push B) X
  refine ⟨Y, fun x => (hY x).trans ?_⟩
  change (M.mem x X ∧ δ.toUnarySchema.denote (ρ.push B) x) ↔ _
  rw [hδ x]
  refine ⟨fun ⟨hx, w, _, hw⟩ => ⟨hx, w, hw⟩, fun ⟨hx, hp⟩ => ?_⟩
  obtain ⟨w, hwB, hw⟩ := hB x hx
  exact ⟨hx, w, hwB, ((ht x w).mp hw).elim id (fun h => ((hc x hx).mp hp ⟨w, h⟩).elim)⟩

/-- Σ₁ 单值关系在集合上的精确像集；收集见证后只需一次 Δ₀ 分离。 -/
theorem s1_image_l (hKP : M.Models KP) {n} (φ : S1_binary n) (ρ : Env M n) (X : M.Domain)
    (ht : ∀ x, M.mem x X → ∃ y, φ.schema.denote ρ x y)
    (hu : ∀ x, M.mem x X → ∀ y z, φ.schema.denote ρ x y → φ.schema.denote ρ x z → y = z) :
    ∃ Y, ∀ y, M.mem y Y ↔ ∃ x, M.mem x X ∧ φ.schema.denote ρ x y := by
  obtain ⟨B, hB⟩ := s1_collection_l hKP φ ρ X ht
  let e : Fin (n + 3) → Fin (n + 5) :=
    Fin.cases 0 (Fin.cases 2 (Fin.cases 1 (fun i => ⟨i.val + 5, by omega⟩)))
  let ψ : Delta0UnarySchema (n + 2) := {
    body := Formula.existsMem (.bound 2) (Formula.existsMem (.bound 2) (φ.matrix.body.rename e))
    freeClosed := by simp -implicitDefEqProofs [φ.matrix.freeClosed]
    delta0 := .existsMem _ (.existsMem _ (φ.matrix.delta0.rename_l e)) }
  let η := (ρ.push X).push B
  have he y x w : (((η.push y).push x).push w).reindex e = ((ρ.push x).push y).push w := by
    rw [Env.mk.injEq]
    exact ⟨funext (Fin.cases rfl (Fin.cases rfl (Fin.cases rfl (fun _ => rfl)))), rfl⟩
  have hψ y : ψ.toUnarySchema.denote η y ↔ ∃ x, M.mem x X ∧ ∃ w, M.mem w B ∧
      Formula.satisfies (((ρ.push x).push y).push w) φ.matrix.body := by
    simp only [UnarySchema.denote, ψ, Formula.satisfies_existsMem_iff, Formula.satisfies_rename, he]
    rfl
  obtain ⟨Y, hY⟩ := separation_exists_d hKP ψ η B
  refine ⟨Y, fun y => (hY y).trans ?_⟩
  change (M.mem y B ∧ ψ.toUnarySchema.denote η y) ↔ _
  rw [hψ y]
  constructor
  · rintro ⟨_, x, hx, w, _, hw⟩
    exact ⟨x, hx, (φ.sat_l ρ x y).mpr ⟨w, hw⟩⟩
  · rintro ⟨x, hx, hy⟩
    obtain ⟨z, hz, w, hwB, hw⟩ := hB x hx
    have heq := hu x hx y z hy ((φ.sat_l ρ x z).mpr ⟨w, hw⟩)
    subst z
    exact ⟨hz, x, hx, w, hwB, hw⟩

theorem d0_image_l (hKP : M.Models KP) {n} (φ : Delta0BinarySchema n) (ρ : Env M n) (X : M.Domain)
    (ht : ∀ x, M.mem x X → ∃ y, φ.toBinarySchema.denote ρ x y)
    (hu : ∀ x, M.mem x X → ∀ y z,
      φ.toBinarySchema.denote ρ x y → φ.toBinarySchema.denote ρ x z → y = z) :
    ∃ Y, ∀ y, M.mem y Y ↔ ∃ x, M.mem x X ∧ φ.toBinarySchema.denote ρ x y := by
  simpa only [S1_binary.of_delta0_sat_l] using
    s1_image_l hKP (S1_binary.of_delta0 φ) ρ X
      (fun x hx => (ht x hx).imp (fun y hy => (S1_binary.of_delta0_sat_l φ ρ x y).mpr hy))
      (fun x hx y z hy hz => hu x hx y z
        ((S1_binary.of_delta0_sat_l φ ρ x y).mp hy) ((S1_binary.of_delta0_sat_l φ ρ x z).mp hz))

end KP
end YesMetaZFC.SetTheory
