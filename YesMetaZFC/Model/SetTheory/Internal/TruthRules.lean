import YesMetaZFC.Model.SetTheory.Internal.Truth

/-! # 编码满足关系的完整逻辑方程

合法指令的子公式编号严格小于当前行，所以先前真值表和完整真值表在这些
编号处一致。由此直接得到关系、等号、或非与存在量词的 Tarski 方程。
-/

namespace YesMetaZFC.SetTheory.Internal
open Definitional.Project
universe u
variable {M : Structure.{u}} {𝒞 : OrderedPairConvention} (I : 𝒞.Interpretation M)

private def Ref_d (k : Nat) (ω r i j : M.Domain) : Prop :=
  match k with
  | 0 | 1 => M.mem i ω ∧ M.mem j ω
  | 2 => M.mem i r ∧ M.mem j r
  | _ => M.mem i ω ∧ M.mem j r

private theorem refs_l (hKP : M.Models KP) {ω r c k i j}
    (hc : Sfm_node_d I ω r c) (hs : Sop_d I k c i j) : Ref_d k ω r i j := by
  rcases hc with ⟨a, b, ht, ha, hb⟩ | ⟨a, b, ht, ha, hb⟩ | ⟨a, b, ht, ha, hb⟩ | ⟨a, b, ht, ha, hb⟩ <;>
    obtain ⟨rfl, rfl, rfl⟩ := sop_injective_l I hKP hs ht <;> exact ⟨ha, hb⟩

private theorem arg_restrict_l {k X R H P ω r f i j} (hP : M.IsRestrictionOf I P H r)
    (hr : Ref_d k ω r i j) : Sarg_d I k X R P f i j ↔ Sarg_d I k X R H f i j := by
  have hp a A (ha : M.mem a r) : M.PairMember I a A P ↔ M.PairMember I a A H :=
    (hP.2 a A).trans ⟨And.right, fun h => ⟨ha, h⟩⟩
  rcases k with _ | (_ | (_ | k))
  · rfl
  · rfl
  · exact exists_congr fun A => exists_congr fun B =>
      and_congr (hp i A hr.1) (and_congr (hp j B hr.2) Iff.rfl)
  · exact exists_congr fun A => and_congr (hp j A hr.2) Iff.rfl

theorem seval_row_l (hZF : M.Models ZF) {ω X R E F n H r c Y}
    (hF : Sfm_d I ω n F) (hH : Seval_d I X R E F n H)
    (hc : M.PairMember I r c F) (hY : M.PairMember I r Y H) (f : M.Domain) :
    M.mem f Y ↔ M.mem f E ∧ Snode_d I X R H c f := by
  obtain ⟨P, hP, _, he⟩ := seval_unfold_l I hZF.1 hF.2.1.2.1 hH hc hY
  refine (he f).trans (and_congr_right fun _ => ?_)
  exact exists_congr fun k => exists_congr fun i => exists_congr fun j => and_congr_right fun hs =>
    arg_restrict_l I hP (refs_l I (ZF.modelsKP hZF) (hF.2.2 r c hc) hs)

/-- 满足关系直接展开为该构造符在唯一真值表中的语义。 -/
theorem ssat_op_l (hZF : M.Models ZF) {ω X R E F n H r c i j}
    (hF : Sfm_d I ω n F) (hH : Seval_d I X R E F n H) (hc : M.PairMember I r c F)
    (k : Fin 4) (hs : Sop_d I k.val c i j) (f : M.Domain) :
    Ssat_d I X R E F n r f ↔ M.mem f E ∧ Sarg_d I k.val X R H f i j := by
  have hr := (hF.2.1.2.2 r).mpr ⟨c, hc⟩
  obtain ⟨Y, hY⟩ := (hH.1.2.2 r).mp hr
  exact (ssat_value_l I hZF hH hY f).trans ((seval_row_l I hZF hF hH hc hY f).trans
    (and_congr Iff.rfl (snode_decode_l I (ZF.modelsKP hZF) k hs)))

/-- 二元关系的编码真值就是解码关系在赋值对象上的真值。 -/
theorem ssat_rel_l (hZF : M.Models ZF) {ω X R E F n H r c i j f x y}
    (hF : Sfm_d I ω n F) (hH : Seval_d I X R E F n H) (hc : M.PairMember I r c F)
    (hs : Sop_d I 0 c i j) (hE : M.IsFunctionSpace I E ω X) (hf : M.mem f E)
    (hi : M.PairMember I i x f) (hj : M.PairMember I j y f) :
    Ssat_d I X R E F n r f ↔ M.PairMember I x y R := by
  rw [ssat_op_l I hZF hF hH hc 0 hs f]
  have hh := (hE f).mp hf
  constructor
  · rintro ⟨_, a, b, ha, hb, hr⟩
    have hx := hh.1.2 i a x ha hi
    have hy := hh.1.2 j b y hb hj
    exact hx ▸ hy ▸ hr
  · exact fun hr => ⟨hf, x, y, hi, hj, hr⟩

theorem ssat_eq_l (hZF : M.Models ZF) {ω X R E F n H r c i j f x y}
    (hF : Sfm_d I ω n F) (hH : Seval_d I X R E F n H) (hc : M.PairMember I r c F)
    (hs : Sop_d I 1 c i j) (hE : M.IsFunctionSpace I E ω X) (hf : M.mem f E)
    (hi : M.PairMember I i x f) (hj : M.PairMember I j y f) :
    Ssat_d I X R E F n r f ↔ x = y := by
  rw [ssat_op_l I hZF hF hH hc 1 hs f]
  have hh := (hE f).mp hf
  exact ⟨fun ⟨_, a, ha, hb⟩ => (hh.1.2 i a x ha hi).symm.trans (hh.1.2 j a y hb hj),
    fun he => ⟨hf, x, hi, he ▸ hj⟩⟩

theorem ssat_nor_l (hZF : M.Models ZF) {ω X R E F n H r c i j f}
    (hF : Sfm_d I ω n F) (hH : Seval_d I X R E F n H) (hc : M.PairMember I r c F)
    (hs : Sop_d I 2 c i j) (hf : M.mem f E) :
    Ssat_d I X R E F n r f ↔ ¬ (Ssat_d I X R E F n i f ∨ Ssat_d I X R E F n j f) := by
  have hr := (hF.2.1.2.2 r).mpr ⟨c, hc⟩
  obtain ⟨hi, hj⟩ := refs_l I (ZF.modelsKP hZF) (hF.2.2 r c hc) hs
  obtain ⟨A, hA⟩ := (hH.1.2.2 i).mp (hH.1.1.transitive r hr i hi)
  obtain ⟨B, hB⟩ := (hH.1.2.2 j).mp (hH.1.1.transitive r hr j hj)
  rw [ssat_op_l I hZF hF hH hc 2 hs f, ssat_value_l I hZF hH hA, ssat_value_l I hZF hH hB]
  constructor
  · rintro ⟨_, A', B', hA', hB', hh⟩
    have he := hH.1.2.1.2 i A' A hA' hA
    have he' := hH.1.2.1.2 j B' B hB' hB
    exact he ▸ he' ▸ hh
  · exact fun h => ⟨hf, A, B, hA, hB, h⟩

/-- 内部存在量词沿实际单坐标更新取投影，包含全部模型对象见证。 -/
theorem ssat_exists_l (hZF : M.Models ZF) {ω X R E F n H r c i j f}
    (hF : Sfm_d I ω n F) (hH : Seval_d I X R E F n H) (hc : M.PairMember I r c F)
    (hs : Sop_d I 3 c i j) (hf : M.mem f E) :
    Ssat_d I X R E F n r f ↔ ∃ x g, M.mem x X ∧ Senv_update_d I f i x g ∧ Ssat_d I X R E F n j g := by
  have hr := (hF.2.1.2.2 r).mpr ⟨c, hc⟩
  have hj := (refs_l I (ZF.modelsKP hZF) (hF.2.2 r c hc) hs).2
  obtain ⟨A, hA⟩ := (hH.1.2.2 j).mp (hH.1.1.transitive r hr j hj)
  rw [ssat_op_l I hZF hF hH hc 3 hs f]
  constructor
  · rintro ⟨_, A', hA', x, g, hx, hg, hh⟩
    have he := hH.1.2.1.2 j A' A hA' hA
    exact ⟨x, g, hx, hg, (ssat_value_l I hZF hH hA g).mpr (he ▸ hh)⟩
  · rintro ⟨x, g, hx, hg, hh⟩
    exact ⟨hf, A, hA, x, g, hx, hg, (ssat_value_l I hZF hH hA g).mp hh⟩

end YesMetaZFC.SetTheory.Internal
