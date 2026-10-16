import YesMetaZFC.SetTheory.LargeCardinal.ExtenderSeedNormal
import YesMetaZFC.SetTheory.Collapse.RelationMap

/-! # 原始关系超幂中的完整支撑初段

坐标类给出 L 的单射像，正规性保证该像对原商中的全部前驱封闭。
倒转坐标图便得到这个初段的实际坍塌；整个商可以仍然不良基。
-/
namespace YesMetaZFC.SetTheory.LargeCardinal
open Definitional.Project InnerModel Internal
universe u
variable {M : Structure.{u}} (hZF : M.Models ZF)
local notation "I" => kp_pair_l (ZF.modelsKP hZF)

theorem ep_seed_segment_l {ω κ K L X R F J O Z A p T S q C W : M.Domain}
    (source : Ep_source_d hZF ω κ K X R) (hκ : M.TransitiveSet κ) (hL : M.TransitiveSet L)
    (hωL : M.MemberSubset ω L) (family : Em_source_d ω κ L X F)
    (coherent : Ec_source_d I ω κ L X F) (atoms : Ea_atoms_d ω κ L F) (normal : En_source_d ω κ L X F)
    (system : Ep_system_d I ω κ L X R F J O Z A p T S) (limit : Di_limit_d A p T S q C W) :
    ∃ B r, M.MemberSubset B C ∧ Wc_map_d B W L r ∧ M.IsSetBijectionFromTo I r B L ∧
      (∀ E α, Rd_entry_d E α r ↔ Ep_seed_d κ L q α E) ∧
      ∀ E H, M.mem E B → Rd_entry_d H E W → M.mem H B := by
  have bound α E (seed : Ep_seed_d κ L q α E) : M.mem α L ∧ M.mem E C := by
    obtain ⟨_, a, i, _, _, ha, hi, _, _, u, B, _, _, hu⟩ := seed
    exact ⟨(ha.bound_l hi).2, (limit.projection.bound_l hu).2⟩
  let ρ : Env M 3 := ⟨Fin.cases κ (Fin.cases L (fun _ => q)), fun _ => L⟩
  let φ : BinarySchema 3 := { body := ep_seed_m (.bound 2) (.bound 3) (.bound 4) (.bound 1) .newest }
  have sat α E : φ.denote ρ α E ↔ Ep_seed_d κ L q α E := ep_seed_sat_l hZF.1 ..
  obtain ⟨i, fi, spec⟩ := ZF.exists_setFunctionFromTo_of_denote hZF I φ ρ (source := L) (target := C)
    (fun α hα => (ep_seed_exists_l hZF source family system limit hα).imp fun E h => (sat α E).mpr h.2)
    (fun α _ E H he hh => (ep_seed_atoms_l hZF source family atoms system limit
      ((sat α E).mp he) ((sat α H).mp hh)).1.mpr rfl)
    (fun α E _ he => (bound α E ((sat α E).mp he)).2)
  have read α E : Rd_entry_d α E i ↔ Ep_seed_d κ L q α E :=
    (spec α E).trans ((and_congr_right fun _ => sat α E).trans
      ⟨And.right, fun seed => ⟨(bound α E seed).1, seed⟩⟩)
  obtain ⟨B, range⟩ := ZF.exists_range_of_setFunction hZF I fi.1 fi.2.1
  have bij : M.IsSetBijectionFromTo I i L B := ⟨⟨⟨fi.1, fi.2.1, fun α hα =>
    (fi.2.2 α hα).imp fun E he => ⟨(range E).mpr ⟨α, he.2⟩, he.2⟩⟩,
    fun α β E hα hβ => (ep_seed_atoms_l hZF source family atoms system limit
      ((read α E).mp hα) ((read β E).mp hβ)).1.mp rfl⟩,
    fun E hE => ((range E).mp hE).imp fun α h => ⟨fi.input_mem_of_pairMember h, h⟩⟩
  obtain ⟨r, fr, inverse⟩ := ZF.exists_inverseBijectionWithPairs hZF I bij
  have decode E α : Rd_entry_d E α r ↔ Ep_seed_d κ L q α E := (inverse E α).trans (read α E)
  have sub E (hE : M.mem E B) : M.mem E C := by
    obtain ⟨α, hα⟩ := (range E).mp hE
    exact fi.output_mem_of_pairMember hα
  have down E H (hE : M.mem E B) (edge : Rd_entry_d H E W) : M.mem H B := by
    obtain ⟨α, hα⟩ := (range E).mp hE
    obtain ⟨β, _, seed⟩ := ep_seed_down_l hZF source hκ hωL family coherent normal system limit ((read α E).mp hα) edge
    exact (range H).mpr ⟨β, (read β H).mpr seed⟩
  refine ⟨B, r, sub, ⟨hL, fn0_of_function_l (ZF.modelsKP hZF) fr.1.1,
    fun α hα => (fr.2 α hα).imp fun _ h => h, ?_⟩, fr, decode, down⟩
  intro E hE α hα hEα β hβ
  constructor
  · intro hβα
    obtain ⟨H, _, hHβ⟩ := fr.2 β hβ
    exact ⟨H, fr.1.1.input_mem_of_pairMember hHβ,
      (ep_seed_atoms_l hZF source family atoms system limit ((decode H β).mp hHβ) ((decode E α).mp hEα)).2.mpr hβα, hHβ⟩
  · rintro ⟨H, _, edge, hHβ⟩
    exact (ep_seed_atoms_l hZF source family atoms system limit ((decode H β).mp hHβ) ((decode E α).mp hEα)).2.mp edge

end YesMetaZFC.SetTheory.LargeCardinal
