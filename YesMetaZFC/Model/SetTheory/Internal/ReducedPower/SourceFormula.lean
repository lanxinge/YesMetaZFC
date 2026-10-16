import YesMetaZFC.Model.SetTheory.Internal.ReducedPower.SourceSatisfaction
import YesMetaZFC.Model.SetTheory.Internal.Compiler
import YesMetaZFC.Model.SetTheory.Internal.FormulaRelation
import YesMetaZFC.Model.SetTheory.Internal.ReducedPower.Restriction

/-! # 原二元公式在源超幂中的逐点解释

编译原公式并实际生成代表赋值，再解码已有的全部内部公式 Łoś 定理。
这允许改变所观察的可定义关系，同时保留原商类和源内部代表族。
-/
namespace YesMetaZFC.SetTheory.Internal
open Definitional.Project InnerModel
universe u
variable {M : Structure.{u}} (hZF : M.Models ZF)
local notation "I" => kp_pair_l (ZF.modelsKP hZF)

theorem rs_formula_l {ω c X R D P U o G p C T f g B H : M.Domain}
    (hω : M.IsOmega ω) (hX : M.TransitiveSet X) (hm : Smem_d I c X R)
    (theory : Sc_theory_d I ω X R) (uniform : Sc_uniform_d I ω X R D)
    (hD : M.mem D X) (hP : FilterZF.Source_d X D P) (hU : FilterZF.Rel_ultra_d D P U)
    (hG : ∀ g, M.mem g G ↔ M.mem g X ∧ Fn0_d D X g) (model : Rp_model_d I D X U R o G p C T)
    (hf : Rd_entry_d f B p) (hg : Rd_entry_d g H p) (φ : Formula 1 2) (hc : φ.FreeClosed) :
    Formula.satisfies (sr_pair_env_l (N := smdl_structure_l I (R := T) model.code.2.1)
      ⟨B, model.map.projection.output_mem_of_pairMember hf⟩
      ⟨H, model.map.projection.output_mem_of_pairMember hg⟩) φ ↔
      ∃ A, M.mem A U ∧ ∀ v, M.mem v A → ∃ x y : (smdl_structure_l I (R := R) hm.1.2.1).Domain,
        Rd_entry_d v x.val f ∧ Rd_entry_d v y.val g ∧
          Formula.satisfies (sr_pair_env_l (N := smdl_structure_l I (R := R) hm.1.2.1) x y) φ := by
  have ext := rf_ext_mem_l I hZF.1 hX hm
  let N := smdl_structure_l I (R := R) hm.1.2.1
  let L := smdl_structure_l I (R := T) model.code.2.1
  obtain ⟨z, n, F, r, k, code, nums, read⟩ := source_compile_l I hZF hω φ hc
  have ki : Function.Injective k := fun i j he => Fin.ext
    (num_injective_l (ZF.modelsKP hZF) (nums i) (he.symm ▸ nums j))
  have kω i := num_mem_l hZF.1 hω (nums i)
  let a : Fin 2 → M.Domain := Fin.cases g (fun _ => f)
  have ha i : M.mem (a i) G := Fin.cases (model.map.projection.input_mem_of_pairMember hg)
    (fun _ => model.map.projection.input_mem_of_pairMember hf) i
  obtain ⟨E₀, he₀⟩ := ZF.exists_functionSpace hZF I ω G
  obtain ⟨t, ht, tk⟩ := senv_params_l I hZF he₀ ⟨f, model.map.projection.input_mem_of_pairMember hf⟩ k a ki kω ha
  obtain ⟨E, e, A, he, ee, ev, ac, los⟩ := rs_los_assignment_l hZF hω hX hm theory uniform hD hP hU hG model ((he₀ t).mp ht)
  have tf : M.IsSetFunctionFromTo I t ω X := ((he₀ t).mp ht).mono_target_l I (fun u hu => ((hG u).mp hu).1)
  have htf := (he t).mpr tf
  let b : Fin 2 → M.Domain := Fin.cases H (fun _ => B)
  have ab i : Rd_entry_d (a i) (b i) p := Fin.cases hg (fun _ => hf) i
  have ek i : Rd_entry_d (k i) (b i) e := by
    obtain ⟨u, V, hku, _, huV, hkV⟩ := ev (k i) (kω i)
    have eu := tf.1.2 (k i) u (a i) hku (tk i)
    exact model.map.projection.1.2 (a i) V (b i) (eu ▸ huV) (ab i) ▸ hkV
  obtain ⟨E₁, he₁⟩ := ZF.exists_functionSpace hZF I ω C
  have de := (satisfies_decode_l I hZF.1 model.code code he₁).trans
    (read C T model.code.2.1 E₁ he₁ e ((he₁ e).mpr ee)
      (sr_pair_env_l (N := L) ⟨B, model.map.projection.output_mem_of_pairMember hf⟩
        ⟨H, model.map.projection.output_mem_of_pairMember hg⟩) (Fin.cases (ek 0) (fun i => ek i.succ)))
  refine de.symm.trans ((los z ((ac z).mpr ⟨n, F, r, code⟩)).trans ?_)
  apply exists_congr
  intro V
  apply and_congr_right
  intro hV
  apply forall_congr'
  intro v
  apply imp_congr_right
  intro hv
  have hvD := hU.base.bounds V hV v hv
  have point u (hu : M.mem u E) (eval : Pe_assign_d I ω D X R t u v)
      (x y : N.Domain) (hx : Rd_entry_d v x.val f) (hy : Rd_entry_d v y.val g) :
      Satisfies_d I ω c z u ↔ Formula.satisfies (sr_pair_env_l (N := N) x y) φ := by
    apply (satisfies_decode_l I hZF.1 hm.1 code he).trans
    apply read X R hm.1.2.1 E he u hu (sr_pair_env_l (N := N) x y)
    intro i
    obtain ⟨q, z', hkq, sf, hvz, hkz⟩ := eval (k i) (kω i)
    have eq := tf.1.2 (k i) q (a i) hkq (tk i)
    subst q
    have val : Rd_entry_d v ((sr_pair_env_l (N := N) x y).bound i).val (a i) := Fin.cases hy (fun _ => hx) i
    exact sf.unique_l I ext hvz ((rf_val_mem_l I hZF.1 hX hm (sf.mem_l I)).mpr val) ▸ hkz
  constructor
  · rintro ⟨u, hu, eval, hs⟩
    obtain ⟨x, hx, hfx⟩ := (model.map.functions f (model.map.projection.input_mem_of_pairMember hf)).2.1 v hvD
    obtain ⟨y, hy, hgy⟩ := (model.map.functions g (model.map.projection.input_mem_of_pairMember hg)).2.1 v hvD
    exact ⟨⟨x, hx⟩, ⟨y, hy⟩, hfx, hgy, (point u hu eval ⟨x, hx⟩ ⟨y, hy⟩ hfx hgy).mp hs⟩
  · rintro ⟨x, y, hx, hy, hs⟩
    obtain ⟨u, hu, eval⟩ := pe_value_exists_l I hZF ext he htf (fun _ h => h) (hX D hD v hvD)
      ((hm.2 v D).mpr ⟨hX D hD v hvD, hD, hvD⟩) (ev.repr_l I tf.1)
    exact ⟨u, hu, eval, (point u hu eval x y hx hy).mpr hs⟩

/-- 原测度可能含源外集合；用否定公式及共同细化消去对源内测度限制的依赖。 -/
theorem rs_formula_relation_l {ω c X R D U o G p C T Q f g B H : M.Domain}
    (hω : M.IsOmega ω) (hX : M.TransitiveSet X) (hm : Smem_d I c X R)
    (theory : Sc_theory_d I ω X R) (uniform : Sc_uniform_d I ω X R D)
    (hD : M.mem D X) (hU : FilterZF.Sf_ultra_d X D U)
    (hG : ∀ g, M.mem g G ↔ M.mem g X ∧ Fn0_d D X g) (model : Rp_model_d I D X U R o G p C T)
    (hf : Rd_entry_d f B p) (hg : Rd_entry_d g H p) (φ : Formula 1 2) (hc : φ.FreeClosed)
    (rel : ∀ x y : (smdl_structure_l I (R := R) hm.1.2.1).Domain, Rd_entry_d x.val y.val Q ↔
      Formula.satisfies (sr_pair_env_l (N := smdl_structure_l I (R := R) hm.1.2.1) x y) φ) :
    Formula.satisfies (sr_pair_env_l (N := smdl_structure_l I (R := T) model.code.2.1)
      ⟨B, model.map.projection.output_mem_of_pairMember hf⟩ ⟨H, model.map.projection.output_mem_of_pairMember hg⟩) φ ↔
      Rp_rel_d I X U Q f g := by
  obtain ⟨P, V, hP, hV, vs, restricted⟩ := rs_restrict_model_l hZF hω hX hm theory hD hU hG model
  have pos := rs_formula_l hZF hω hX hm theory uniform hD hP hV hG restricted hf hg φ hc
  have neg := rs_formula_l hZF hω hX hm theory uniform hD hP hV hG restricted hf hg (.neg φ)
    (by simpa only [Definitional.Formula.FreeClosed] using hc)
  constructor
  · intro hs
    obtain ⟨A, hA, spec⟩ := pos.mp hs
    exact ⟨A, ((vs A).mp hA).2, fun v hv => by
      obtain ⟨x, y, hx, hy, hs⟩ := spec v hv
      exact ⟨x.val, x.property, y.val, y.property, hx, hy, (rel x y).mpr hs⟩⟩
  · intro hs
    apply Classical.byContradiction
    intro no
    obtain ⟨A, hA, spec⟩ := neg.mp ((Formula.satisfies_neg_iff ..).mpr no)
    obtain ⟨E, hE, point⟩ := hs
    obtain ⟨B, hB, ba, be⟩ := hU.base.meet A E ((vs A).mp hA).2 hE
    obtain ⟨v, hv⟩ := hU.proper B hB
    obtain ⟨x, y, hx, hy, hn⟩ := spec v (ba v hv)
    obtain ⟨x', hx', y', hy', hfx, hgy, hxy⟩ := point v (be v hv)
    have ex := (fn0_function_l (ZF.modelsKP hZF) (model.map.functions f
      (model.map.projection.input_mem_of_pairMember hf))).1.2 v x' x.val hfx hx
    have ey := (fn0_function_l (ZF.modelsKP hZF) (model.map.functions g
      (model.map.projection.input_mem_of_pairMember hg))).1.2 v y' y.val hgy hy
    exact (Formula.satisfies_neg_iff ..).mp hn ((rel x y).mp (ex ▸ ey ▸ hxy))

end YesMetaZFC.SetTheory.Internal
