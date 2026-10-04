import YesMetaZFC.SetTheory.LargeCardinal.ExtenderAlgebra
import YesMetaZFC.SetTheory.LargeCardinal.ExtenderSeeds
import YesMetaZFC.SetTheory.Descriptive.Prefix

/-! # 有限列表示中的前缀投影与末项唯一性 -/
namespace YesMetaZFC.SetTheory.LargeCardinal
open Definitional.Project InnerModel Internal
universe u
variable {M : Structure.{u}}

theorem ex_append_unique_l (hE : Extensional M) {n m κ s t u x : M.Domain}
    (hm : M.SuccessorOf m n) (hs : Fn0_d n κ s) (ht : Fn0_d m κ t) (hu : Fn0_d m κ u)
    (hst : M.MemberSubset s t) (hsu : M.MemberSubset s u) (hnt : Rd_entry_d n x t) (hnu : Rd_entry_d n x u) : t = u := by
  apply ht.ext_l hE hu
  intro i hi
  rcases (hm i).mp hi with hin | he
  · obtain ⟨y, _, hiy⟩ := hs.2.1 i hin
    exact ⟨y, hiy.elim fun p hp => ⟨p, hp.1, hst p hp.2⟩, hiy.elim fun p hp => ⟨p, hp.1, hsu p hp.2⟩⟩
  · have e := hE.eq_of_same_members i n he
    exact ⟨x, e ▸ hnt, e ▸ hnu⟩

theorem ex_prefix_cp_l (hE : Extensional M) {n m κ q s t : M.Domain}
    (hq : ∀ i j, Rd_entry_d i j q ↔ M.mem i n ∧ i = j) (hnm : M.MemberSubset n m)
    (ht : Fn0_d n κ t) : Cp0_d n m κ q s t ↔ M.MemberSubset t s := by
  constructor
  · intro h p hp
    obtain ⟨i, hi, x, hx, hc⟩ := ht.1 p hp
    obtain ⟨j, _, y, hy, hij, hjy, hiy⟩ := h.2 i hi
    have e := ((hq i j).mp hij).2
    subst j
    have ey := ht.2.2 i hi y hy x hx hiy ⟨p, hc, hp⟩
    obtain ⟨r, hr, hrs⟩ := (ey ▸ hjy : Rd_entry_d i x s)
    exact kpair_unique_l M hE hr hc ▸ hrs
  · intro sub
    refine ⟨ht, fun i hi => ?_⟩
    obtain ⟨x, hx, hix⟩ := ht.2.1 i hi
    exact ⟨i, hnm i hi, x, hx, (hq i i).mpr ⟨hi, rfl⟩,
      hix.elim (fun p hp => ⟨p, hp.1, sub p hp.2⟩), hix⟩

theorem ex_prefix_pull_l (hZF : M.Models ZF) {ω κ L F n m a b U V A : M.Domain}
    (hc : Es_coherent_d (kp_pair_l (ZF.modelsKP hZF)) ω κ L F)
    (hn : M.mem n ω) (hm : M.mem m ω) (hnm : M.MemberSubset n m)
    (ha : Fn0_d n L a) (hb : Fn0_d m L b) (hab : M.MemberSubset a b)
    (haU : Rd_entry_d a U F) (hbV : Rd_entry_d b V F) (hA : ∀ t, M.mem t A → Fn0_d n κ t) :
    ∃ Z, (∀ s, M.mem s Z ↔ Fn0_d m κ s ∧ ∃ t, M.mem t A ∧ M.MemberSubset t s) ∧
      (M.mem Z V ↔ M.mem A U) := by
  let I := kp_pair_l (ZF.modelsKP hZF)
  let φ : BinarySchema 0 := { body := Formula.extensionalEq (.bound 1) .newest }
  let ρ : Env M 0 := ⟨Fin.elim0, fun _ => n⟩
  have sat i j : φ.denote ρ i j ↔ i = j := Formula.satisfies_extensionalEq_iff_eq hZF.1 _ _ _
  obtain ⟨q, hq, qs⟩ := ZF.exists_setFunctionFromTo_of_denote hZF I φ ρ (source := n) (target := m)
    (fun i _ => ⟨i, (sat i i).mpr rfl⟩) (fun i _ j k hj hk => ((sat i j).mp hj).symm.trans ((sat i k).mp hk))
    (fun i j hi hij => (sat i j).mp hij ▸ hnm i hi)
  have spec i j : Rd_entry_d i j q ↔ M.mem i n ∧ i = j := (qs i j).trans (and_congr_right fun _ => sat i j)
  obtain ⟨Z, hz, hu⟩ := hc n m q b a U V A hn hm (fn0_of_function_l (ZF.modelsKP hZF) hq) hb
    ((ex_prefix_cp_l hZF.1 spec hnm ha).mpr hab) hbV haU hA
  exact ⟨Z, fun s => (hz s).trans (and_congr_right fun _ => exists_congr fun t =>
    and_congr_right fun ht => ex_prefix_cp_l hZF.1 spec hnm (hA t ht)), hu⟩

end YesMetaZFC.SetTheory.LargeCardinal
