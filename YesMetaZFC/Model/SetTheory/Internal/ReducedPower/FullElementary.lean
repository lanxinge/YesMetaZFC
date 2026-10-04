import YesMetaZFC.Model.SetTheory.Internal.ReducedPower.Restriction
import YesMetaZFC.Model.SetTheory.Internal.ReducedPower.Projection

/-! # 完整测度下既有商投影的全部内部初等性

限制到源内子集代数后，模型码与代表图保持原样。源内部投影定理给出
初等图，再用商提升的唯一性识别为既有投影。
-/
namespace YesMetaZFC.SetTheory.Internal
open Definitional.Project InnerModel FilterZF
universe u
variable {M : Structure.{u}} (hZFC : M.Models ZFC)
local notation "hZF" => ZFC.models_zf_l hZFC
local notation "I" => kp_pair_l (ZF.modelsKP hZF)

theorem rs_full_projection_l {ω χ c d X R H S e D₀ D₁ Q₀ Q₁ U V t o₀ o₁ G₀ G₁ p₀ p₁ C₀ C₁ T₀ T₁ K j : M.Domain}
    (hω : M.IsOmega ω) (hχ : M.IsRegularCardinal I χ) (hωχ : M.mem ω χ) (hH : H_d I χ H)
    (hX : M.TransitiveSet X) (hm : Smem_d I c X R) (hn : Smem_d I d H S) (he : Smap_d I ω c d X H e)
    (hD₀ : M.mem D₀ X) (hD₁ : M.mem D₁ X) (htX : M.mem t X)
    (hQ₀ : M.IsPowerSetOf Q₀ D₀) (hU : Maximal_d (ℳ := M) D₀ U) (hV : Maximal_d (ℳ := M) D₁ V)
    (ht : Push_d D₀ D₁ Q₀ Q₁ U V t)
    (hG₀ : ∀ f, M.mem f G₀ ↔ M.mem f X ∧ Fn0_d D₀ X f) (hG₁ : ∀ f, M.mem f G₁ ↔ M.mem f X ∧ Fn0_d D₁ X f)
    (hM₀ : Rp_model_d I D₀ X U R o₀ G₀ p₀ C₀ T₀) (hM₁ : Rp_model_d I D₁ X V R o₁ G₁ p₁ C₁ T₁)
    (hK : M.IsSetFunctionFromTo I K G₀ G₁)
    (spec : ∀ f g, M.PairMember I f g K ↔ M.mem f G₀ ∧ M.mem g G₁ ∧ Cp0_d D₁ D₀ X t f g)
    (hj : M.IsSetFunctionFromTo I j C₀ C₁) (lift : Rp_lift_d I K p₀ p₁ j) : Smap_d I ω o₀ o₁ C₀ C₁ j := by
  obtain ⟨P₀, U', hp₀, hu, us, model₀⟩ := rs_restrict_model_l hZFC hω hχ hωχ hH hX hm hn he hD₀ hU hG₀ hM₀
  obtain ⟨P₁, V', hp₁, hv, vs, model₁⟩ := rs_restrict_model_l hZFC hω hχ hωχ hH hX hm hn he hD₁ hV hG₁ hM₁
  have push : Push_d D₀ D₁ P₀ P₁ U' V' t := by
    refine ⟨ht.1, fun A ha => ?_⟩
    obtain ⟨B, hBX, hb⟩ := smap_pull_l I hZF hω hχ.isLimitOrdinal hH hX hm hn he hD₁ htX ((hp₀ A).mp ha).1
    have hBP := (hp₁ B).mpr ⟨hBX, fun v hv => ((hb v).mp hv).1⟩
    obtain ⟨B', _, hb', eq⟩ := ht.2 A ((hQ₀ A).mpr ((hp₀ A).mp ha).2)
    have eb := hZF.1.eq_of_same_members B' B (fun v => (hb' v).trans (hb v).symm)
    subst B'
    have left : M.mem B V' ↔ M.mem B V := (vs B).trans ⟨And.right, fun h => ⟨hBP, h⟩⟩
    have right : M.mem A U' ↔ M.mem A U := (us A).trans ⟨And.right, fun h => ⟨ha, h⟩⟩
    exact ⟨B, hBP, hb, left.trans (eq.trans right.symm)⟩
  obtain ⟨K', j', hk', ks, elem, lift'⟩ := rs_projection_embedding_l hZFC hω hχ hωχ hH hX hm hn he
    hD₀ hD₁ htX hp₀ hp₁ hu hv push hG₀ hG₁ model₀ model₁
  have ek := hk'.1.1.eq_of_pairMember_iff hZF.1 hK.1.1 (fun f g => (ks f g).trans (spec f g).symm)
  subst K'
  exact rp_lift_unique_l I hZF.1 hM₀.map hM₁.map hK elem.1.1 hj lift' lift ▸ elem

end YesMetaZFC.SetTheory.Internal
