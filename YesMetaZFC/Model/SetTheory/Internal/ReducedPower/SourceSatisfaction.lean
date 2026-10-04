import YesMetaZFC.Model.SetTheory.Internal.ReducedPower.SourceLos
import YesMetaZFC.Model.SetTheory.Internal.ReducedPower.SourceAssignment

/-! # 全部源内部公式代码的商满足关系

同一个实际代表赋值投影为同一个商赋值。逐公式取得有限支撑后应用行定理，
再用全坐标逐点赋值消去支撑参数，得到统一满足关系上的完整 Łoś 方程。
-/
namespace YesMetaZFC.SetTheory.Internal
open Definitional.Project InnerModel
universe u
variable {M : Structure.{u}} (hZFC : M.Models ZFC)
local notation "hZF" => ZFC.models_zf_l hZFC
local notation "I" => kp_pair_l (ZF.modelsKP hZF)
variable {ω χ c d X R H S q D P U o G p C T E}
    (hω : M.IsOmega ω) (hχ : M.IsRegularCardinal (kp_pair_l (ZF.modelsKP (ZFC.models_zf_l hZFC))) χ) (hωχ : M.mem ω χ)
    (hH : H_d (kp_pair_l (ZF.modelsKP (ZFC.models_zf_l hZFC))) χ H) (hX : M.TransitiveSet X)
    (hm : Smem_d (kp_pair_l (ZF.modelsKP (ZFC.models_zf_l hZFC))) c X R)
    (hn : Smem_d (kp_pair_l (ZF.modelsKP (ZFC.models_zf_l hZFC))) d H S)
    (hq : Smap_d (kp_pair_l (ZF.modelsKP (ZFC.models_zf_l hZFC))) ω c d X H q)
    (hD : M.mem D X) (hP : FilterZF.Source_d X D P)
    (hU : FilterZF.Rel_ultra_d D P U) (hG : ∀ g, M.mem g G ↔ M.mem g X ∧ Fn0_d D X g)
    (hM : Rp_model_d (kp_pair_l (ZF.modelsKP (ZFC.models_zf_l hZFC))) D X U R o G p C T)
    (hE : M.IsFunctionSpace (kp_pair_l (ZF.modelsKP (ZFC.models_zf_l hZFC))) E ω X)
include hω hχ hωχ hH hX hm hn hq hD hP hU hG hM hE

theorem rs_satisfies_l {A a e z} (hA : Scode_d I ω A) (ha : M.mem a E)
    (he : M.IsSetFunctionFromTo I e ω C) (hv : Rs_eval_d I ω D X p a e) (hz : M.mem z A) :
    Satisfies_d I ω o z e ↔ ∃ B, M.mem B U ∧ ∀ v, M.mem v B →
      ∃ f, M.mem f E ∧ Pe_assign_d I ω D X a f v ∧ Satisfies_d I ω c z f := by
  obtain ⟨n, F, r, hf⟩ := (hA z).mp hz
  obtain ⟨b, hb, hB⟩ := sbound_exists_l I hZF hω hf.2.1
  obtain ⟨K, hK⟩ := ZF.exists_functionSpace hZF I ω C
  have bω := hω.transitive hZF b hb
  have repr := hv.repr_l I ((hE a).mp ha).1
  have los := rs_los_l hZFC hω hχ hωχ hH hX hm hn hq hD hP hU hG hM hE hK hf.2.1 hb hB hf.2.2
    a e ha ((hK e).mpr he) (fun i hi => hv i (bω i hi))
  refine (satisfies_decode_l I hZF.1 hM.code hf hK).trans (los.symm.trans ?_)
  apply exists_congr
  intro B
  apply and_congr_right
  intro hB'
  apply forall_congr'
  intro v
  apply imp_congr_right
  intro hvB
  have hvD := hU.base.bounds B hB' v hvB
  apply (pe_sat_full_l I hZF hX hE hf.2.1 hB bω hf.2.2 ha repr hvD hm.1.2.1).trans
  exact exists_congr fun f => and_congr_right fun _ => and_congr_right fun _ =>
    (satisfies_decode_l I hZF.1 hm.1 hf hE).symm

omit hE in
/-- 从实际 ω→G 代表赋值图一次构造赋值空间、商赋值和全部公式码。 -/
theorem rs_los_assignment_l {a} (ha : M.IsSetFunctionFromTo I a ω G) : ∃ E e A,
    M.IsFunctionSpace I E ω X ∧ M.IsSetFunctionFromTo I e ω C ∧ Rs_eval_d I ω D X p a e ∧ Scode_d I ω A ∧
    ∀ z, M.mem z A → (Satisfies_d I ω o z e ↔ ∃ B, M.mem B U ∧ ∀ v, M.mem v B →
      ∃ f, M.mem f E ∧ Pe_assign_d I ω D X a f v ∧ Satisfies_d I ω c z f) := by
  obtain ⟨E, hE⟩ := ZF.exists_functionSpace hZF I ω X
  have hax : M.IsSetFunctionFromTo I a ω X := ⟨ha.1, ha.2.1, fun i hi =>
    (ha.2.2 i hi).imp fun g hg => ⟨((hG g).mp hg.1).1, hg.2⟩⟩
  have hr : Pe_repr_d I ω D X a := fun i g _ hg => by
    obtain ⟨hgX, hgD⟩ := (hG g).mp (ha.output_mem_of_pairMember hg)
    exact smap_function_domain_l hZFC hω hχ hωχ hH hX hm hn hq hD hgX hgD
  obtain ⟨e, he, hv⟩ := rs_eval_exists_l I hZF hX hG hM.map hE ((hE a).mpr hax) hr
  obtain ⟨A, hA⟩ := scode_exists_l I hZF hω
  exact ⟨E, e, A, hE, he, hv, hA, fun z hz => rs_satisfies_l hZFC hω hχ hωχ hH hX hm hn hq hD hP hU hG hM hE
    hA ((hE a).mpr hax) he hv hz⟩

end YesMetaZFC.SetTheory.Internal
