import YesMetaZFC.SetTheory.LargeCardinal.ExtenderFunctionCode
import YesMetaZFC.SetTheory.Card.FiniteSequenceJoin

/-! # 两段有限坐标的实际分块投影

序数加法只用于定位第二段；编码对象仍是有限函数图。返回两张投影图，
并实际拼接任意两段 κ 值列，供集合值代表的图编码使用。
-/
namespace YesMetaZFC.SetTheory.LargeCardinal
open Definitional.Project InnerModel Internal
universe u
variable {M : Structure.{u}}

theorem ep_tuple_l (hZF : M.Models ZF) {ω κ n m : M.Domain} (hω : M.IsOmega ω)
    (hn : M.mem n ω) (hm : M.mem m ω) : ∃ l q r, M.mem l ω ∧ Fn0_d n l q ∧ Fn0_d m l r ∧
      ∀ s t, Fn0_d n κ s → Fn0_d m κ t → ∃ u, Fn0_d l κ u ∧ Cp0_d n l κ q u s ∧ Cp0_d m l κ r u t := by
  let I := kp_pair_l (ZF.modelsKP hZF)
  have mo := hω.members_areOrdinals hZF m hm
  obtain ⟨l, hl, unique⟩ := ZF.ordinalAddition_existsUnique hZF I n mo
  have hlω := ZF.ordinalAddition_mem_omega hZF I hω hn hm hl
  let ρ : Env M 0 := ⟨Fin.elim0, fun _ => n⟩
  have idread i j := Formula.denote_identityValue_iff hZF.1 ρ i j
  obtain ⟨q, hq, qs⟩ := ZF.exists_setFunctionFromTo_of_denote hZF I BinarySchema.identityValue ρ (source := n) (target := l)
    (fun i _ => ⟨i, (idread i i).mpr rfl⟩) (fun i _ j k hj hk => ((idread i j).mp hj).symm.trans ((idread i k).mp hk))
    (fun i j hi hij => (idread i j).mp hij ▸ (ZF.ordinalAddition_mem_iff hZF I mo hl).mpr (Or.inl hi))
  have qread i j : Rd_entry_d i j q ↔ M.mem i n ∧ i = j := (qs i j).trans (and_congr_right fun _ => idread i j)
  let η : Env M 1 := ⟨fun _ => n, fun _ => n⟩
  let φ : BinarySchema 1 := { body := Formula.isOrdinalAddition kpair_convention_l .newest (.bound 2) (.bound 1) }
  have sat i j : φ.denote η i j ↔ M.IsOrdinalAddition I j n i := Formula.satisfies_isOrdinalAddition_iff I hZF.1 ..
  obtain ⟨r, hr, rs⟩ := ZF.exists_setFunctionFromTo_of_denote hZF I φ η (source := m) (target := l)
    (fun i hi => (ZF.ordinalAddition_existsUnique hZF I n (mo.mem hi)).imp fun j hj => (sat i j).mpr hj.1)
    (fun i hi j k hj hk => by
      obtain ⟨v, _, uniq⟩ := ZF.ordinalAddition_existsUnique hZF I n (mo.mem hi)
      exact (uniq j ((sat i j).mp hj)).trans (uniq k ((sat i k).mp hk)).symm)
    (fun i j hi hj => (ZF.ordinalAddition_mem_iff hZF I mo hl).mpr (Or.inr ⟨i, hi, (sat i j).mp hj⟩))
  have rread i j : Rd_entry_d i j r ↔ M.mem i m ∧ M.IsOrdinalAddition I j n i :=
    (rs i j).trans (and_congr_right fun _ => sat i j)
  refine ⟨l, q, r, hlω, fn0_of_function_l (ZF.modelsKP hZF) hq, fn0_of_function_l (ZF.modelsKP hZF) hr, fun s t hs ht => ?_⟩
  obtain ⟨l', u, _, hl', hu, head, tail⟩ := ZF.fseq_join_l I hZF hω hn hm
    (fn0_function_l (ZF.modelsKP hZF) hs) (fn0_function_l (ZF.modelsKP hZF) ht)
  have el := unique l' hl'
  subst l'
  refine ⟨u, fn0_of_function_l (ZF.modelsKP hZF) hu, ⟨hs, fun i hi => ?_⟩, ht, fun i hi => ?_⟩
  · obtain ⟨x, hx, hix⟩ := hs.2.1 i hi
    exact ⟨i, (ZF.ordinalAddition_mem_iff hZF I mo hl).mpr (Or.inl hi), x, hx,
      (qread i i).mpr ⟨hi, rfl⟩, ((head.2 i x).mp hix).2, hix⟩
  · obtain ⟨x, hx, hix⟩ := ht.2.1 i hi
    obtain ⟨_, j, hj, hju⟩ := (tail.2 i x).mp hix
    exact ⟨j, (ZF.ordinalAddition_mem_iff hZF I mo hl).mpr (Or.inr ⟨i, hi, hj⟩), x, hx,
      (rread i j).mpr ⟨hi, hj⟩, hju, hix⟩

end YesMetaZFC.SetTheory.LargeCardinal
