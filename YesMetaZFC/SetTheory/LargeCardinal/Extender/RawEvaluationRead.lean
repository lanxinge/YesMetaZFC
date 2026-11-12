import YesMetaZFC.SetTheory.LargeCardinal.Extender.RawEvaluation
import YesMetaZFC.SetTheory.LargeCardinal.Extender.BoundedGraph

/-! # 工作模型中原池求值的实际代表

工作所属模型具有真实隶属表示时，恒等数字坐标还原原支撑，
恒等共同图还原同一个原函数。原池节点因此给出同一超幂代表，
不要求整个原关系后继先作传递坍塌。
-/
namespace YesMetaZFC.SetTheory.LargeCardinal
open Definitional.Project InnerModel Internal
universe u
variable {M : Structure.{u}} (hZF : M.Models ZF)
local notation "I" => kp_pair_l (ZF.modelsKP hZF)

theorem Er_eval_d.read_mem_l {ω c N T L z Γ Y k q u E : M.Domain}
    (hω : M.IsOmega ω) (trans : M.TransitiveSet N) (model : Smem_d I c N T)
    (inside : M.MemberSubset Γ N)
    (numbers : ∀ n m, Rd_entry_d n m z ↔ M.mem n ω ∧ n = m)
    (identity : ∀ x y, Rd_entry_d x y k → x = y)
    (value : Er_eval_d I ω L N T z Γ Y k q u E) : Eb_value_d q u E := by
  obtain ⟨α, a, f, d, D, F, g, code, pair, fn, dc, fF, graph, comp, rep⟩ := value
  let ρ : Env M 3 := ⟨Fin.cases u (Fin.cases a (fun _ => f)), fun _ => u⟩
  have literal : Formula.satisfies ρ (kpair0_m .newest (.bound 1) (.bound 2)) :=
    ((rr_truth_mem_l I trans model (kpair0_m .newest (.bound 1) (.bound 2)) (kpair0_delta_l ..) ρ.bound).mp pair).2
  have actualPair : KPair_d M u a f := (kpair0_sat_l hZF.1 ρ .newest (.bound 1) (.bound 2)).mp literal
  obtain ⟨n, m, hn, fa, hnm, fnA, ga⟩ := code
  obtain ⟨_, rfl⟩ := (numbers n m).mp hnm
  have aa := ((rf_fun_mem_l I hZF.1 trans model fnA.1).mp fnA).function_l trans
  have eq := aa.ext_l hZF.1 fa (fun i hi => by
    obtain ⟨x, _, hix⟩ := fa.2.1 i hi
    exact ⟨x, (rf_val_mem_l I hZF.1 trans model (fnA.mem_l I)).mp
      ((ga i i x ((numbers i i).mpr ⟨hω.transitive (ZF.modelsKP hZF) n hn i hi, rfl⟩)).mp hix), hix⟩)
  subst α
  have eq : D = d := hZF.1.eq_of_same_members D d (fun s => (dc s).trans
    ⟨fun h => ((model.2 s d).mp h.2).2.2,
      fun hs => ⟨trans d fn.1 s hs, (model.2 s d).mpr ⟨trans d fn.1 s hs, fn.1, hs⟩⟩⟩)
  subst D
  have ff := ((rf_fun_mem_l I hZF.1 trans model fn.1).mp fn).function_l trans
  have eq := fF.ext_l hZF.1 ff (fun s hs => by
    obtain ⟨x, hx, hsx⟩ := fF.2.1 s hs
    exact ⟨x, hsx, (rf_val_mem_l I hZF.1 trans model (fn.mem_l I)).mp
      ((graph s x (trans d fn.1 s hs) (inside x hx)).mp hsx)⟩)
  subst F
  have eq := comp.1.ext_l hZF.1 ff (fun s hs => by
    obtain ⟨x, _, y, _, hsx, hxy, hsy⟩ := comp.2 s hs
    exact ⟨y, hsy, identity x y hxy ▸ hsx⟩)
  subst g
  exact ⟨a, f, actualPair, rep⟩

end YesMetaZFC.SetTheory.LargeCardinal
