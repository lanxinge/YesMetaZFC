import YesMetaZFC.SetTheory.CumulativeRank
import YesMetaZFC.SetTheory.Definitional.Project.Predicate

/-! # 可定义非空类的最早层候选集合

在第一个含见证的累积层中分离全部见证，得到唯一、非空的模型内集合。
这是 Scott 式集合收紧：不从中任选一个元素，也不假定全局选择函数。
-/

namespace YesMetaZFC.SetTheory
open Definitional.Project
universe u
variable {M : Structure.{u}} {𝒞 : OrderedPairConvention} (I : 𝒞.Interpretation M)

def V_hits_d {n} (φ : UnarySchema n) (ρ : Env M n) (α : M.Domain) : Prop :=
  ∃ V, V_d I α V ∧ ∃ x, M.mem x V ∧ φ.denote ρ x

def V_min_d {n} (φ : UnarySchema n) (ρ : Env M n) (α S : M.Domain) : Prop :=
  ∃ V, V_d I α V ∧ (∃ x, M.mem x S) ∧ (∀ x, M.mem x S ↔ M.mem x V ∧ φ.denote ρ x) ∧
    ∀ β, V_hits_d I φ ρ β → M.MemberSubset α β

def v_hits_m (𝒞 : OrderedPairConvention) {k n} (φ : UnarySchema k) (e : Fin k → Term n) (α : Term n) : Formula 1 n :=
  .existsE (.conj (v_m 𝒞 α.weaken .newest) (.existsE (.conj (.mem .newest (.bound 1))
    (pred_m φ (fun i => (e i).weaken.weaken) .newest))))
@[simp] theorem v_hits_closed_l (𝒞 : OrderedPairConvention) {k n} (φ : UnarySchema k) (e : Fin k → Term n) (α : Term n)
    (he : ∀ i, (e i).freeSupport = []) (hα : α.freeSupport = []) : (v_hits_m 𝒞 φ e α).FreeClosed := by
  simp -implicitDefEqProofs [v_hits_m, Definitional.Formula.FreeClosed, he, hα]

def v_min_m (𝒞 : OrderedPairConvention) {k n} (φ : UnarySchema k) (e : Fin k → Term n) (α S : Term n) : Formula 1 n :=
  .existsE (.conj (v_m 𝒞 α.weaken .newest) (.conj (.existsE (.mem .newest S.weaken.weaken))
    (.conj (.forallE (.iff (.mem .newest S.weaken.weaken) (.conj (.mem .newest (.bound 1))
      (pred_m φ (fun i => (e i).weaken.weaken) .newest))))
      (.forallE (.imp (v_hits_m 𝒞 φ (fun i => (e i).weaken.weaken) .newest) (Formula.subset α.weaken.weaken .newest))))))
@[simp] theorem v_min_closed_l (𝒞 : OrderedPairConvention) {k n} (φ : UnarySchema k) (e : Fin k → Term n) (α S : Term n)
    (he : ∀ i, (e i).freeSupport = []) (hα : α.freeSupport = []) (hS : S.freeSupport = []) :
    (v_min_m 𝒞 φ e α S).FreeClosed := by
  simp -implicitDefEqProofs [v_min_m, Definitional.Formula.FreeClosed, he, hα, hS]

theorem v_hits_sat_l (hE : Extensional M) {k n} (φ : UnarySchema k) (ρ : Env M n) (e : Fin k → Term n) (α : Term n) :
    Formula.satisfies ρ (v_hits_m 𝒞 φ e α) ↔
      V_hits_d I φ (⟨fun i => (e i).eval ρ, ρ.free⟩ : Env M k) (α.eval ρ) := by
  simp only [v_hits_m, V_hits_d, Formula.satisfies_exists_iff, Formula.satisfies_conj_iff,
    v_sat_l I hE, Formula.satisfies_mem_iff, pred_sat_l M,
    Definitional.Term.eval_weaken, Definitional.Term.eval_newest]
  rfl

theorem v_min_sat_l (hE : Extensional M) {k n} (φ : UnarySchema k) (ρ : Env M n) (e : Fin k → Term n) (α S : Term n) :
    Formula.satisfies ρ (v_min_m 𝒞 φ e α S) ↔
      V_min_d I φ (⟨fun i => (e i).eval ρ, ρ.free⟩ : Env M k) (α.eval ρ) (S.eval ρ) := by
  simp only [v_min_m, V_min_d, Formula.satisfies_exists_iff, Formula.satisfies_conj_iff,
    v_sat_l I hE, Formula.satisfies_forall_iff, Formula.satisfies_iff_iff, Formula.satisfies_mem_iff,
    pred_sat_l M, Formula.satisfies_imp_iff, v_hits_sat_l I hE, Formula.satisfies_subset_iff,
    Definitional.Term.eval_weaken, Definitional.Term.eval_newest]
  rfl

theorem v_min_congr_l {n m} {φ : UnarySchema n} {ψ : UnarySchema m} {ρ : Env M n} {η : Env M m}
    (h : ∀ x, φ.denote ρ x ↔ ψ.denote η x) (α S) : V_min_d I φ ρ α S ↔ V_min_d I ψ η α S := by
  have go {n m} {φ : UnarySchema n} {ψ : UnarySchema m} {ρ : Env M n} {η : Env M m}
      (h : ∀ x, φ.denote ρ x ↔ ψ.denote η x) (hs : V_min_d I φ ρ α S) : V_min_d I ψ η α S := by
    obtain ⟨V, hV, hn, hS, hl⟩ := hs
    refine ⟨V, hV, hn, fun x => (hS x).trans (and_congr_right fun _ => h x), ?_⟩
    rintro β ⟨W, hW, x, hx, hψ⟩
    exact hl β ⟨W, hW, x, hx, (h x).mpr hψ⟩
  exact ⟨go h, go (fun x => (h x).symm)⟩

namespace ZF

theorem v_min_exists_l (hZF : M.Models ZF) {n} (φ : UnarySchema n) (ρ : Env M n)
    (hne : ∃ x, φ.denote ρ x) : ∃ α S, V_min_d I φ ρ α S := by
  obtain ⟨x, hx⟩ := hne
  obtain ⟨γ, V, hV, hxV⟩ := v_cover_l I hZF x
  obtain ⟨δ, hδ⟩ := KP.exists_successor (modelsKP hZF) γ
  have hδo := KP.successor_isOrdinal (modelsKP hZF) (v_ordinal_l I hV) hδ
  let e : Fin n → Term (n+1) := fun i => .bound ⟨i.val+1, by omega⟩
  let θ : UnarySchema n := {
    body := v_hits_m 𝒞 φ e .newest
    freeClosed := v_hits_closed_l _ _ _ _ (fun _ => rfl) rfl }
  have hθ β : θ.denote ρ β ↔ V_hits_d I φ ρ β := by
    have he : (⟨fun i => (e i).eval (ρ.push β), (ρ.push β).free⟩ : Env M n) = ρ := by cases ρ; rfl
    exact (v_hits_sat_l I hZF.1 φ (ρ.push β) e .newest).trans (by rw [he]; rfl)
  obtain ⟨A, hA'⟩ := separation_exists_d hZF θ ρ δ
  have hA β : M.mem β A ↔ M.mem β δ ∧ V_hits_d I φ ρ β :=
    (hA' β).trans (and_congr_right fun _ => hθ β)
  obtain ⟨α, hα, hLeast⟩ := hδo.wellOrder.least A (fun β hβ => ((hA β).mp hβ).1)
    ⟨γ, (hA γ).mpr ⟨hδ.predecessor_mem, V, hV, x, hxV, hx⟩⟩
  obtain ⟨W, hW, y, hyW, hy⟩ := ((hA α).mp hα).2
  obtain ⟨S, hS⟩ := separation_exists_d hZF φ ρ W
  refine ⟨α, S, W, hW, ⟨y, (hS y).mpr ⟨hyW, hy⟩⟩, hS, ?_⟩
  rintro β ⟨U, hU, z, hzU, hz⟩
  have of_le (hle : M.SameMembers α β ∨ M.mem α β) : M.MemberSubset α β := by
    rcases hle with hle | hle
    · exact fun i hi => (hle i).mp hi
    · exact (v_ordinal_l I hU).transitive.memberSubset hle
  rcases Structure.IsOrdinal.trichotomy hZF.1 (v_ordinal_l I hW) (v_ordinal_l I hU)
      (KP.difference_exists_d (modelsKP hZF)) (KP.intersection_exists_d (modelsKP hZF) α β) with he | he | he
  · exact of_le (Or.inl he)
  · exact of_le (Or.inr he)
  · exact of_le (hLeast β ((hA β).mpr ⟨hδo.transitive α ((hA α).mp hα).1 β he, U, hU, z, hzU, hz⟩))

theorem v_min_unique_l (hZF : M.Models ZF) {n} {φ : UnarySchema n} {ρ : Env M n} {α S β T}
    (h : V_min_d I φ ρ α S) (h' : V_min_d I φ ρ β T) : α = β ∧ S = T := by
  obtain ⟨V, hV, ⟨x, hx⟩, hS, hα⟩ := h
  obtain ⟨W, hW, ⟨y, hy⟩, hT, hβ⟩ := h'
  have hab := hα β ⟨W, hW, y, (hT y).mp hy⟩
  have hba := hβ α ⟨V, hV, x, (hS x).mp hx⟩
  have he := hZF.1.eq_of_same_members α β (fun i => ⟨hab i, hba i⟩)
  subst β
  have he := v_unique_l I hZF hV hW
  subst W
  exact ⟨rfl, hZF.1.eq_of_same_members S T (fun z => (hS z).trans (hT z).symm)⟩

end ZF
end YesMetaZFC.SetTheory
