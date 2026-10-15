import YesMetaZFC.SetTheory.LargeCardinal.TypeGameVacuous
import YesMetaZFC.SetTheory.Descriptive.TreeShift

/-! # 6.10 的连续代换与投影

在实数和标签组成的节点前加任意一项。逆向构造首个标签时，从已有分支的首项读取，
因此不额外假设标签字母表非空。
-/
namespace YesMetaZFC.SetTheory.LargeCardinal
open Definitional.Project InnerModel Internal Descriptive
universe u
variable {M : Structure.{u}} (hZF : M.Models ZF)
local notation "I" => kp_pair_l (ZF.modelsKP hZF)

theorem tp_shift_projection_l {ω A Γ Y F T S z a f g : M.Domain} (hw : M.IsOmega ω)
    (hz : ∀ x, ¬ M.mem x z) (ha : M.mem a A) (pair : M.IsCartesianProduct I Y A Γ)
    (space : Fseq_space_d I ω Y F) (subT : M.MemberSubset T F) (shift : Tr_shift_d I z F T S)
    (ff : M.IsSetFunctionFromTo I f ω A) (fg : M.IsSetFunctionFromTo I g ω A) (cons : Cons_d I z a f g) :
    Tp_projection_d I ω A Y F S g ↔ Tp_projection_d I ω A Y F T f := by
  constructor
  · rintro ⟨q', fq', branch, left⟩
    obtain ⟨v, q, hv, fq, cq⟩ := tail_omega_l I hZF hw hz fq'
    refine ⟨q, fq, (shift.branch_l I hZF hw hz hv space subT cq).mp branch, ff, fun i x => ⟨?_, ?_⟩⟩
    · intro ix
      have hi := ff.input_mem_of_pairMember ix
      obtain ⟨j, sj, _⟩ := hw.1.2 i hi
      obtain ⟨p, c, jp, cp⟩ := (left.2 j x).mp ((cons.successor_l I hZF hw hz hi sj).mpr ix)
      exact ⟨p, c, (cq.successor_l I hZF hw hz hi sj).mp jp, cp⟩
    · rintro ⟨p, c, ip, cp⟩
      have hi := fq.input_mem_of_pairMember ip
      obtain ⟨j, sj, _⟩ := hw.1.2 i hi
      exact (cons.successor_l I hZF hw hz hi sj).mp
        ((left.2 j x).mpr ⟨p, c, (cq.successor_l I hZF hw hz hi sj).mpr ip, cp⟩)
  · rintro ⟨q, fq, branch, left⟩
    obtain ⟨z', hz', hzω⟩ := hw.1.1
    have eq := hZF.1.eq_of_same_members z' z fun x => iff_of_false (hz' x) (hz x); subst z'
    obtain ⟨p, hp, _⟩ := fq.2.2 z hzω
    obtain ⟨_, _, c, hc, _⟩ := (pair p).mp hp
    obtain ⟨v, cv⟩ := (I).total a c
    have hv := (pair v).mpr ⟨a, ha, c, hc, cv⟩
    obtain ⟨q', fq', cq⟩ := cons_omega_l I hZF hw hz hv fq
    refine ⟨q', fq', (shift.branch_l I hZF hw hz hv space subT cq).mpr branch, fg, fun j x => ⟨?_, ?_⟩⟩
    · intro jx
      rcases (cons.2 j x).mp jx with ⟨rfl, rfl⟩ | ⟨i, ix, sj⟩
      · exact ⟨v, c, (cq.2 _ v).mpr (Or.inl ⟨rfl, rfl⟩), cv⟩
      · obtain ⟨p, c, ip, cp⟩ := (left.2 i x).mp ix
        exact ⟨p, c, (cq.2 j p).mpr (Or.inr ⟨i, ip, sj⟩), cp⟩
    · rintro ⟨p, c', jp, cp⟩
      rcases (cq.2 j p).mp jp with ⟨rfl, rfl⟩ | ⟨i, ip, sj⟩
      · have eq := ((I).injective cv cp).1
        exact (cons.2 _ x).mpr (Or.inl ⟨rfl, eq.symm⟩)
      · exact (cons.2 j x).mpr (Or.inr ⟨i, (left.2 i x).mpr ⟨p, c', ip, cp⟩, sj⟩)

end YesMetaZFC.SetTheory.LargeCardinal
