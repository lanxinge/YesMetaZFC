import YesMetaZFC.Model.SetTheory.Internal.DeltaCode
import YesMetaZFC.Model.SetTheory.Internal.SourceTheory
import YesMetaZFC.Model.SetTheory.Internal.EmbeddingOmega

/-! # 源中有界关系的实际分离

固定有界原公式先编译为内部程序，再消费源自身的全内部分离模式。
传递性把内部有界真值还原为背景真值，整个构造只需 ZF。
-/
namespace YesMetaZFC.SetTheory.Internal
open Definitional.Project InnerModel
universe u
variable {M : Structure.{u}} {𝒞 : OrderedPairConvention} (I : 𝒞.Interpretation M)

/-- 任意原公式在源中的相对分离；全部模型内量词保留，尚不作绝对性假设。 -/
theorem sc_separate_relative_l (hZF : M.Models ZF) {ω c X R D}
    (hω : M.IsOmega ω) (hm : Smem_d I c X R) (theory : Sc_theory_d I ω X R)
    (hn : Nonempty {x : M.Domain // M.mem x X}) {p} (φ : UnarySchema p)
    (ρ : Env (rt_model_l X hn) p) (hD : M.mem D X) :
    ∃ A, M.mem A X ∧ M.MemberSubset A D ∧ ∀ x : (rt_model_l X hn).Domain,
      M.mem x.val A ↔ M.mem x.val D ∧ φ.denote ρ x := by
  obtain ⟨z, hz⟩ := hm.1.2.1
  obtain ⟨e, he⟩ := KP.exists_empty (ZF.modelsKP hZF)
  let ψ := spred_core_l (source_core_l φ.body)
  have closed := spred_core_closed_l (source_core_l φ.body) (source_core_closed_l φ.body φ.freeClosed)
  obtain ⟨a, n, F, r, v, hF, hv, hc⟩ := source_compile_l I hZF hω ψ closed
  have hinj : Function.Injective v := fun i j h => Fin.ext (num_injective_l (ZF.modelsKP hZF) (hv i) (h.symm ▸ hv j))
  have hωv i := num_mem_l hZF.1 hω (hv i)
  obtain ⟨E, hE⟩ := ZF.exists_functionSpace hZF I ω X
  obtain ⟨f, hf, hp⟩ := senv_params_l I hZF hE hm.1.2.1 v
    (fun i => ((ρ.push ⟨z, hz⟩).bound i).val) hinj hωv (fun i => ((ρ.push ⟨z, hz⟩).bound i).property)
  have read (x : (rt_model_l X hn).Domain) g (hu : Senv_update_d I f (v 0) x.val g) :
      Ssat_d I X R E F n r g ↔ φ.denote ρ x := by
    have params : ∀ i, M.PairMember I (v i) ((ρ.push x).bound i).val g := Fin.cases
      ((hu.2 (v 0) x.val).mpr (Or.inl ⟨rfl, rfl⟩)) (fun i =>
        (hu.2 (v i.succ) (ρ.bound i).val).mpr (Or.inr ⟨fun h => Fin.succ_ne_zero i (hinj h), hp i.succ⟩))
    exact (hc X R hm.1.2.1 E hE g ((hE g).mpr (hu.function_l I ((hE f).mp hf) (hωv 0) x.property))
      ⟨(ρ.push x).bound, (ρ.push x).free⟩ params).trans
      ((spred_core_sat_l I (ZF.modelsKP hZF) (hm.empty_pred_l I he) hn (source_core_l φ.body) (ρ.push x)).trans
        (source_core_sat_l φ.body (ρ.push x)))
  obtain ⟨A, hAX, spec⟩ := theory.separation E F n r (v 0) f D hE hF.2.1 hF.2.2 (hωv 0) hf hD
  refine ⟨A, hAX, fun x hx => ((spec x).mp hx).1, fun x => (spec x.val).trans (and_congr_right fun _ => ?_)⟩
  refine ⟨fun ⟨g, hu, ht⟩ => (read x g hu).mp ht, fun ht => ?_⟩
  obtain ⟨g, hu, _⟩ := senv_update_exists_l I hZF ((hE f).mp hf) (hωv 0) x.property
  exact ⟨g, hu, (read x g hu).mpr ht⟩

theorem sc_separate_source_l (hZF : M.Models ZF) {ω c X R D}
    (hω : M.IsOmega ω) (hX : M.TransitiveSet X) (hm : Smem_d I c X R) (theory : Sc_theory_d I ω X R)
    {p} (φ : UnarySchema p) (hd : φ.body.IsDelta0) (ρ : Env M p)
    (hρ : ∀ i, M.mem (ρ.bound i) X) (hD : M.mem D X) :
    ∃ A, M.mem A X ∧ ∀ x, M.mem x A ↔ M.mem x D ∧ φ.denote ρ x := by
  obtain ⟨z, hz⟩ := hm.1.2.1
  let hn : Nonempty {x // M.mem x X} := ⟨⟨z, hz⟩⟩
  let η : Env (rt_model_l X hn) p := ⟨fun i => ⟨ρ.bound i, hρ i⟩, fun _ => ⟨z, hz⟩⟩
  have read x (hx : M.mem x X) : φ.denote η ⟨x, hx⟩ ↔ φ.denote ρ x :=
    (rt_model_delta_l hX hn hd (η.push ⟨x, hx⟩)).trans
      (Formula.closed_env_l φ.body φ.freeClosed (funext (Fin.cases rfl (fun _ => rfl))))
  obtain ⟨A, hA, sub, spec⟩ := sc_separate_relative_l I hZF hω hm theory hn φ η hD
  exact ⟨A, hA, fun x => ⟨fun hx =>
    ⟨sub x hx, (read x (hX A hA x hx)).mp ((spec ⟨x, hX A hA x hx⟩).mp hx).2⟩,
    fun ⟨hx, ht⟩ => (spec ⟨x, hX D hD x hx⟩).mpr ⟨hx, (read x (hX D hD x hx)).mpr ht⟩⟩⟩

end YesMetaZFC.SetTheory.Internal
