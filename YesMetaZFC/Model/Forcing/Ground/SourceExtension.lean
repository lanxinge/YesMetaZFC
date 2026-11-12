import YesMetaZFC.Model.Forcing.Extension.GenericSet
import YesMetaZFC.Model.Forcing.Functions.ValueIsomorphism
import YesMetaZFC.Model.Forcing.Ground.ProductProjection
import YesMetaZFC.Model.Forcing.Ground.CheckPool
import YesMetaZFC.Model.SetTheory.Embedding.Reflect

/-! # 大扩张内原源模型、实际泛型集合及指定名字的同一呈示

源载体直接取规范像 j(X)，不要求它在扩张中仍为完整秩层。原模型和此
集合模型由实际满同构识别；泛型集合的精确成员方程同时识别两个滤子。
因此原指定名字的完整背景图可直接交给大扩张内的构枝定理。
-/
namespace YesMetaZFC.Model.Forcing.Internal
open SetTheory SetTheory.Definitional.Project SetTheory.InnerModel SetTheory.Internal
universe u
variable {M : Structure.{u}} (hZF : M.Models ZF) {c X R : M.Domain}
  (source : Smem_d (kp_pair_l (ZF.modelsKP hZF)) c X R) (trans : M.TransitiveSet X)
  (native : (smdl_structure_l (kp_pair_l (ZF.modelsKP hZF)) (R := R) source.1.2.1).Models ZF)
local notation "I" => kp_pair_l (ZF.modelsKP hZF)
local notation "N" => smdl_structure_l I (R := R) (And.left (And.right (And.left source)))
include trans

theorem Smem_d.extension_source_l {B T z : (N).Domain} (O : Cond_order_d N B T z)
    {H : M.Domain → Prop} (generic : Generic_d M B.val T.val z.val H)
    (j : M.Domain → (extension_l M hZF B.val T.val z.val H).Domain) (ji : Function.Injective j)
    (jf : ∀ a y, y ∈ j a ↔ ∃ b, M.mem b a ∧ j b = y)
    (ground : ∀ a, Gval_d M B.val T.val z.val H a (j a)) :
    let E := extension_l M hZF B.val T.val z.val H
    let O' := image_cond_order_l (ZF.modelsKP native) hZF.1 Subtype.val (fun _ _ eq => Subtype.ext eq) (smem_full_l I source trans) O
    let hE := preserves_zf_l O' hZF generic
    ∃ source' : Smem_d (kp_pair_l (ZF.modelsKP hE)) (j c) (j X) (j R), E.TransitiveSet (j X) ∧
      ∃ native' : (smdl_structure_l (kp_pair_l (ZF.modelsKP hE)) (R := j R) source'.1.2.1).Models ZF,
      ∃ F : E.Domain, Gset_d (j B.val) (j T.val) (j z.val) (j X) F ∧
      ∃ e : (N).Domain → (smdl_structure_l (kp_pair_l (ZF.modelsKP hE)) (R := j R) source'.1.2.1).Domain,
        (∀ a, (e a).val = j a.val) ∧ Function.Surjective e ∧ Pe_d e ∧
        (∀ p, E.mem (e p).val F ↔ H p.val) ∧
        Generic_d (smdl_structure_l (kp_pair_l (ZF.modelsKP hE)) (R := j R) source'.1.2.1)
          (e B) (e T) (e z) (fun p => E.mem p.val F) ∧
        ∀ ω τ x, Fn_value_d native (j ∘ Subtype.val) B T z ω τ (H ∘ Subtype.val) x →
          Fn_value_d native' Subtype.val (e B) (e T) (e z) (e ω) (e τ) (fun p => E.mem p.val F) x := by
  let E := extension_l M hZF B.val T.val z.val H
  have ni : Function.Injective (Subtype.val : (N).Domain → M.Domain) := fun _ _ eq => Subtype.ext eq
  have nf := smem_full_l I source trans
  have O' := image_cond_order_l (ZF.modelsKP native) hZF.1 Subtype.val ni nf O
  have hE := preserves_zf_l O' hZF generic
  have source' := image_smem_l j ji jf (ZF.modelsKP hZF) (ZF.modelsKP hE) source
  have trans' := image_transitive_l j jf trans
  have native' := image_smdl_models_l j ji jf (ZF.modelsKP hZF) (ZF.modelsKP hE) source.1 native
  obtain ⟨F,members,filter⟩ := generic.value_set_l hZF O' j ground
  obtain ⟨e,_,onto,fixed,mem⟩ := image_smdl_iso_l j ji jf (ZF.modelsKP hZF) (ZF.modelsKP hE) source.1
  have elem : Pe_d e := fun φ _ ρ => formula_image_l e onto mem φ ρ
  have trace p : E.mem (e p).val F ↔ H p.val := by
    rw [fixed]
    exact (members (j p.val)).trans
      ⟨fun ⟨q,hq,eq⟩ => ji eq ▸ hq,fun hp => ⟨p.val,hp,rfl⟩⟩
  have code : Gset_d (e B).val (e T).val (e z).val (j X) F := by
    simpa only [fixed] using filter X
  have target := ((source'.generic_code_l (kp_pair_l (ZF.modelsKP hE)) hE.1 trans' (ZF.modelsKP native') (e B) (e T) (e z) F).mp code).2
  have g := generic.ground_pull_l (ZF.modelsKP native) hZF.1 Subtype.val ni nf
  refine ⟨source',trans',native',F,filter X,e,fixed,onto,elem,trace,target,fun ω τ x named => ?_⟩
  exact named.iso_l native native' e onto mem O g target (fun p hp => (trace p).mpr hp) fixed

end YesMetaZFC.Model.Forcing.Internal
