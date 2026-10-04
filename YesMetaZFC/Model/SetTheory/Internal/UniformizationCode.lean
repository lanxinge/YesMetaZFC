import YesMetaZFC.Model.SetTheory.Internal.CollectionCode
import YesMetaZFC.Model.SetTheory.Internal.FunctionCode

/-! # 全内部公式的统一函数图代码

把有序对成员条件与原公式合取，再要求所选图是 D 上、某个源内集合中的函数。
函数图坐标在原支撑之外，函数值和原公式的两个变量使用不同坐标。
-/
namespace YesMetaZFC.SetTheory.Internal
open Definitional.Project InnerModel
universe u
variable {M : Structure.{u}} {𝒞 : OrderedPairConvention} (I : 𝒞.Interpretation M)

def Suniform_d (X R E F n r i j f D C B : M.Domain) : Prop := Fn0_d D C B ∧
  ∀ x y, Rd_entry_d x y B → Sbin_d I X R E F n r i j f x y

theorem sfm_uniform_l (hZF : M.Models ZF) {ω n F r i j s t u σ b} (hω : M.IsOmega ω)
    (hF : Sfm_d I ω n F) (hr : M.mem r n) (hσ : M.mem σ ω)
    (hi : M.mem i σ) (hj : M.mem j σ) (hs : M.mem s σ) (ht : M.mem t σ) (hu : M.mem u σ)
    (hij : i ≠ j) (hsi : s ≠ i) (hti : t ≠ i) (htj : t ≠ j) (hst : s ≠ t) (hus : u ≠ s) (hut : u ≠ t)
    (hb : Sbound_d I F b) (htb : ¬ M.mem t b) : ∃ m G k, Sbuild_d I ω n F m G k ∧ ∀ X R E c f D,
      M.TransitiveSet X → Smem_d I c X R → M.IsFunctionSpace I E ω X → M.mem f E → M.PairMember I s D f →
      (Ssat_d I X R E G m k f ↔ ∃ B C, M.mem B X ∧ M.mem C X ∧ Suniform_d I X R E F n r i j f D C B) := by
  have into a (ha : M.mem a σ) := hω.transitive hZF σ hσ a ha
  let p : Fin 3 → M.Domain := Fin.cases i (Fin.cases j (fun _ => t))
  let a : Formula 1 3 := rd_entry0_m (.bound 0) (.bound 1) (.bound 2)
  obtain ⟨n₁, F₁, r₁, h₁, a₁⟩ := sfm_delta_l I hZF hω hF a (by simp -implicitDefEqProofs [a]) (rd_entry0_delta_l ..)
    p hσ (Fin.cases hi (Fin.cases hj (fun _ => ht)))
  obtain ⟨n₂, F₂, r₂, h₂, a₂⟩ := sfm_and_l I hZF hω h₁.program h₁.root (h₁.span r hr)
  obtain ⟨n₃, F₃, r₃, h₃, a₃⟩ := sfm_total_l I hZF hω h₂.program h₂.root (into i hi) (into j hj) (into s hs) hsi
  obtain ⟨n₅, F₅, r₅, h₅, a₅⟩ := sfm_function_l I hZF hω h₃.program hσ ht hs hu hus hut
  obtain ⟨n₆, F₆, r₆, h₆, a₆⟩ := sfm_and_l I hZF hω h₅.program (h₅.span r₃ h₃.root) h₅.root
  obtain ⟨m, G, k, h₇, a₇⟩ := sfm_ex_l I hZF hω h₆.program (into t ht) h₆.root
  refine ⟨m, G, k, ((((h₁.comp I h₂).comp I h₃).comp I h₅).comp I h₆).comp I h₇,
    fun X R E c f D hX hm hE hf hD => ?_⟩
  have hDX := ((hE f).mp hf).output_mem_of_pairMember hD
  have body B g (hBX : M.mem B X) (hg : Senv_update_d I f t B g) :
      Ssat_d I X R E F₆ n₆ r₆ g ↔ ∃ C, M.mem C X ∧ Suniform_d I X R E F n r i j f D C B := by
    have hgE := (hE g).mpr (hg.function_l I ((hE f).mp hf) (into t ht) hBX)
    have hsD := (hg.2 s D).mpr (Or.inr ⟨hst, hD⟩)
    have htB := (hg.2 t B).mpr (Or.inl ⟨rfl, rfl⟩)
    have point x y (hx : M.mem x X) (hy : M.mem y X) :
        Sbin_d I X R E F₂ n₂ r₂ i j g x y ↔ Rd_entry_d x y B ∧ Sbin_d I X R E F n r i j f x y := by
      obtain ⟨v, hv, hvf⟩ := senv_update_exists_l I hZF ((hE g).mp hgE) (into i hi) hx
      obtain ⟨w, hw, hwf⟩ := senv_update_exists_l I hZF hvf (into j hj) hy
      let ρ : Env M 3 := ⟨Fin.cases x (Fin.cases y (fun _ => B)), fun _ => B⟩
      have hp : ∀ z, M.PairMember I (p z) (ρ.bound z) w := Fin.cases
        ((hw.2 i x).mpr (Or.inr ⟨hij, (hv.2 i x).mpr (Or.inl ⟨rfl, rfl⟩)⟩))
        (Fin.cases ((hw.2 j y).mpr (Or.inl ⟨rfl, rfl⟩)) (fun _ => (hw.2 t B).mpr
          (Or.inr ⟨htj, (hv.2 t B).mpr (Or.inr ⟨hti, htB⟩)⟩)))
      have atom : Ssat_d I X R E F₁ n₁ r₁ w ↔ Rd_entry_d x y B :=
        (a₁ X R E c w ρ hX hm hE ((hE w).mpr hwf) hp).trans (rd_entry0_sat_l hZF.1 ..)
      have val : Sbin_d I X R E F n r i j f x y ↔ Ssat_d I X R E F n r w :=
        (sbin_agree_l I hZF hF hb hr (into i hi) (into j hj) hE hf hgE (hg.agree_l I htb) hx hy).trans
          (sbin_value_l I hZF.1 hv hw)
      apply (sbin_value_l I hZF.1 hv hw).trans
      rw [a₂ X R E w ((hE w).mpr hwf), ← h₁.sat_l I hZF hF hr X R E w]
      exact and_congr atom val.symm
    rw [a₆ X R E g hgE, ← h₅.sat_l I hZF h₃.program h₃.root X R E g,
      a₃ X R E c g D hX hm hE hgE hsD, a₅ X R E c g B D hX hm hE hgE htB hsD]
    constructor
    · rintro ⟨hh, _, C, hC, hBC⟩
      refine ⟨C, hC, hBC, fun x y hxy => ?_⟩
      obtain ⟨z, hz, hp⟩ := hh x (hBC.bound_l hxy).1
      obtain ⟨hxz, hφ⟩ := (point x z (hX D hDX x (hBC.bound_l hxy).1) hz).mp hp
      exact hBC.2.2 x (hBC.bound_l hxy).1 z (hBC.bound_l hxz).2 y (hBC.bound_l hxy).2 hxz hxy ▸ hφ
    · rintro ⟨C, hC, hBC, hh⟩
      refine ⟨fun x hx => ?_, hBX, C, hC, hBC⟩
      obtain ⟨y, hy, hxy⟩ := hBC.2.1 x hx
      exact ⟨y, hX C hC y hy, (point x y (hX D hDX x hx) (hX C hC y hy)).mpr ⟨hxy, hh x y hxy⟩⟩
  rw [a₇ X R E f hf]
  constructor
  · rintro ⟨B, g, hB, hg, hh⟩
    obtain ⟨C, hC, hc⟩ := (body B g hB hg).mp hh
    exact ⟨B, C, hB, hC, hc⟩
  · rintro ⟨B, C, hB, hC, hh⟩
    obtain ⟨g, hg, _⟩ := senv_update_exists_l I hZF ((hE f).mp hf) (into t ht) hB
    exact ⟨B, g, hB, hg, (body B g hB hg).mpr ⟨C, hC, hh⟩⟩

end YesMetaZFC.SetTheory.Internal
