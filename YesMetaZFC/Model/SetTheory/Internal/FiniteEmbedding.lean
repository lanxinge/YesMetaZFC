import YesMetaZFC.Model.SetTheory.Internal.FiniteTruth
import YesMetaZFC.Model.SetTheory.Internal.PredicateEmbedding
import YesMetaZFC.SetTheory.InnerModel.Recursion.Composition

/-! # 完整初等嵌入作用于有限赋值

有限参数列先延拓，再沿实际嵌入复合；有限支撑真值比较消去所选尾部。
结论量化全部内部程序，为尝试树每个节点的初等检验提供真实实例。
-/
namespace YesMetaZFC.SetTheory.Internal
open Definitional.Project InnerModel
universe u
variable {M : Structure.{u}} (hZF : M.Models ZF)
local notation "I" => kp_pair_l (ZF.modelsKP hZF)

theorem Smap_d.finite_sat_l {ω c d A R B S j b E D F n r s t : M.Domain}
    (hω : M.IsOmega ω) (hm : Smdl_d I c A R) (hn : Smdl_d I d B S) (hj : Smap_d I ω c d A B j)
    (hb : M.mem b ω) (hF : Sfm_d I ω n F) (bound : Sbound_d I F b) (hr : M.mem r n)
    (hE : M.IsFunctionSpace I E b A) (hD : M.IsFunctionSpace I D b B)
    (hs : Fn0_d b A s) (ht : Cp0_d b A B s j t) :
    Ssat_d I A R E F n r s ↔ Ssat_d I B S D F n r t := by
  obtain ⟨a, ha⟩ := hm.2.1
  obtain ⟨f, fill, hf⟩ := senv_fill_exists_l I hZF (ω := ω) (fn0_function_l (ZF.modelsKP hZF) hs) ha
  obtain ⟨g, hg, assign⟩ := smap_assign_exists_l I hZF hj.1.1 hf
  obtain ⟨E₀, hE₀⟩ := ZF.exists_functionSpace hZF I ω A
  obtain ⟨D₀, hD₀⟩ := ZF.exists_functionSpace hZF I ω B
  have agree : Senv_agree_d I b f s := fun i x hi => (fill.2 i x).trans
    ⟨fun h => h.2.elim And.right (fun h => (h.1 hi).elim), fun h => ⟨hω.transitive hZF b hb i hi, Or.inl ⟨hi, h⟩⟩⟩
  have agree' : Senv_agree_d I b g t := by
    intro i y hi
    obtain ⟨x, hx, hix⟩ := hs.2.1 i hi
    obtain ⟨v, hv, hiv⟩ := ht.1.2.1 i hi
    have hxv := (ht.value_l hs (fn0_of_function_l (ZF.modelsKP hZF) hj.1.1) hix).mp hiv
    have hig := assign i (hω.transitive hZF b hb i hi) x v ((agree i x hi).mpr hix) hxv
    exact ⟨fun h => hg.1.2 i v y hig h ▸ hiv,
      fun h => ht.1.2.2 i hi v hv y (ht.1.bound_l h).2 hiv h ▸ hig⟩
  have left := ssat_spaces_l I hZF (R := R) hF bound hE₀ hE (hω.transitive hZF b hb) (fun _ h => h)
    hr ((hE₀ f).mpr hf) ((hE s).mpr (fn0_function_l (ZF.modelsKP hZF) hs)) agree
  have right := ssat_spaces_l I hZF (R := S) hF bound hD₀ hD (hω.transitive hZF b hb) (fun _ h => h)
    hr ((hD₀ g).mpr hg) ((hD t).mpr (fn0_function_l (ZF.modelsKP hZF) ht.1)) agree'
  exact left.symm.trans ((hj.ssat_l I hZF.1 hm hn hF hr hE₀ hD₀ ((hE₀ f).mpr hf) ((hD₀ g).mpr hg) assign).trans right)

end YesMetaZFC.SetTheory.Internal
