import YesMetaZFC.SetTheory.InnerModel.OD.Source

/-! # 单序数 OD 定义码

把层高度、公式码和参数列码再次规范配对。合法代码的求值是单值的，其值域
恰为 OD；不合法代码不指定值。Minimum 与 Order 据此构造最小代表和良序，
Complexity 将该解码公式有界化，取得整个 OD 类的 Σ₂ 证书。
-/
namespace YesMetaZFC.SetTheory.InnerModel
open Definitional.Project
universe u
variable {M : Structure.{u}} {𝒞 : OrderedPairConvention} (I : 𝒞.Interpretation M)

def Od_eval_d (q x : M.Domain) : Prop := ∃ θ z p t,
  Oc_pair_d I θ z t ∧ Oc_pair_d I t p q ∧ Od_code_d I θ z p x

def od_eval_m {d} (q x : Term d) : Formula 1 d :=
  .existsE (.existsE (.existsE (.existsE
    (.conj (oc_pair_m (𝒞 := 𝒞) (.bound 3) (.bound 2) .newest)
    (.conj (oc_pair_m (𝒞 := 𝒞) .newest (.bound 1) q.weaken.weaken.weaken.weaken)
      (od_code_m (𝒞 := 𝒞) (.bound 3) (.bound 2) (.bound 1) x.weaken.weaken.weaken.weaken))))))
derive_free_closed od_eval_m

theorem od_eval_sat_l (hE : Extensional M) {d} (ρ : Env M d) (q x : Term d) :
    Formula.satisfies ρ (od_eval_m (𝒞 := 𝒞) q x) ↔ Od_eval_d I (q.eval ρ) (x.eval ρ) := by
  simp only [od_eval_m, Od_eval_d, Formula.satisfies_exists_iff, Formula.satisfies_conj_iff,
    oc_pair_sat_l I hE, od_code_sat_l I hE, Definitional.Term.eval_weaken]
  rfl

theorem od_eval_ordinal_l (hZF : M.Models ZF) {q x} (h : Od_eval_d I q x) : M.IsOrdinal q := by
  obtain ⟨_, _, _, _, _, h, _⟩ := h
  exact (oc_pair_types_l I hZF h).2.2

theorem od_eval_unique_l (hZF : M.Models ZF) {q x y}
    (hx : Od_eval_d I q x) (hy : Od_eval_d I q y) : x = y := by
  obtain ⟨θ, z, p, t, ht, hq, hx⟩ := hx
  obtain ⟨β, w, r, u, hu, hq', hy⟩ := hy
  obtain ⟨rfl, rfl⟩ := oc_pair_injective_l I hZF hq hq'
  obtain ⟨rfl, rfl⟩ := oc_pair_injective_l I hZF ht hu
  exact od_code_unique_l I hZF hx hy

theorem od_eval_range_l (hZF : M.Models ZF) {x} : Od_in_d I x ↔ ∃ q, Od_eval_d I q x := by
  constructor
  · rintro ⟨θ, z, p, h⟩
    obtain ⟨hθ, hz, hp⟩ := od_code_types_l I hZF h
    obtain ⟨t, ht⟩ := oc_pair_exists_l I hZF hθ hz
    obtain ⟨q, hq⟩ := oc_pair_exists_l I hZF (oc_pair_types_l I hZF ht).2.2 hp
    exact ⟨q, θ, z, p, t, ht, hq, h⟩
  · exact fun ⟨_, θ, z, p, _, _, _, h⟩ => ⟨θ, z, p, h⟩

/-- 每个 OD 对象都由这一条固定原公式和一个序数参数唯一指定。 -/
def od_eval_s (𝒞 : OrderedPairConvention) : UnarySchema 1 := {
  body := od_eval_m (𝒞 := 𝒞) (.bound 1) .newest }

theorem od_one_parameter_l (hZF : M.Models ZF) {x} : Od_in_d I x ↔
    ∃ q, M.IsOrdinal q ∧ ∀ y, (od_eval_s 𝒞).denote (⟨fun _ => q, fun _ => q⟩ : Env M 1) y ↔ y = x := by
  constructor
  · intro h
    obtain ⟨q, hq⟩ := (od_eval_range_l I hZF).mp h
    refine ⟨q, od_eval_ordinal_l I hZF hq, fun y => ?_⟩
    exact (od_eval_sat_l I hZF.1 _ _ _).trans
      ⟨fun hy => od_eval_unique_l I hZF hy hq, fun he => he.symm ▸ hq⟩
  · rintro ⟨q, _, h⟩
    exact (od_eval_range_l I hZF).mpr ⟨q, (od_eval_sat_l I hZF.1 _ _ _).mp ((h x).mpr rfl)⟩

end YesMetaZFC.SetTheory.InnerModel
