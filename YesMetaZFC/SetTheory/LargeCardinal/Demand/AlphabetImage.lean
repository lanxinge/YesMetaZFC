import YesMetaZFC.Model.SetTheory.Demand.Reply
import YesMetaZFC.Model.SetTheory.Embedding.Theory
import YesMetaZFC.SetTheory.LargeCardinal.Iteration.Step

/-! # 实际原边保持同一树的两个最小字母域

四个坐标依次为树、第一字母域、第二字母域和选定字母。全称定义沿给定
根图或父边搬运，因而目标中的新字母也受最小性及不交性约束；无需枚举
字母域，也不向所属模型额外赋予整体嵌入。
-/
namespace YesMetaZFC.SetTheory.LargeCardinal
open Definitional.Project InnerModel Internal
universe u
variable {M : Structure.{u}} (hZF : M.Models ZF)
local notation "I" => kp_pair_l (ZF.modelsKP hZF)

theorem Smap_d.demand_alphabet_l {ω c X R d Y S j : M.Domain}
    (hw : M.IsOmega ω) (mx : Smdl_d I c X R) (my : Smdl_d I d Y S)
    (map : Smap_d I ω c d X Y j)
    (ext : Extensional (smdl_structure_l I (R := R) mx.2.1))
    (v : Fin 4 → (smdl_structure_l I (R := R) mx.2.1).Domain)
    (w : Fin 4 → (smdl_structure_l I (R := S) my.2.1).Domain)
    (points : ∀ i, Rd_entry_d (v i).val (w i).val j)
    (alphabet : Td_alphabet_d (v 0) (v 1) (v 2))
    (disjoint : ∀ x, (smdl_structure_l I (R := R) mx.2.1).mem x (v 1) →
      ¬ (smdl_structure_l I (R := R) mx.2.1).mem x (v 2))
    (chosen : (smdl_structure_l I (R := R) mx.2.1).mem (v 3) (v 1)) :
    Td_alphabet_d (w 0) (w 1) (w 2) ∧
      (∀ x, (smdl_structure_l I (R := S) my.2.1).mem x (w 1) →
        ¬ (smdl_structure_l I (R := S) my.2.1).mem x (w 2)) ∧
      (smdl_structure_l I (R := S) my.2.1).mem (w 3) (w 1) := by
  -- 源外延性经同一实际边产生目标外延性，不增加目标集合论公理。
  have rawExt : Rf_ext_d I X R := fun a ha b hb same => congrArg Subtype.val
    (ext.eq_of_same_members ⟨a,ha⟩ ⟨b,hb⟩ (fun z => same z.val z.property))
  have targetRaw : Rf_ext_d I Y S := map.extensional_l hZF hw mx my rawExt
  have targetExt := targetRaw.native_l I my.2.1
  let ρ : Env (smdl_structure_l I (R := R) mx.2.1) 4 := ⟨v,fun _ => v 0⟩
  let η : Env (smdl_structure_l I (R := S) my.2.1) 4 := ⟨w,fun _ => w 0⟩
  have transfer (φ : Formula 1 4) (closed : φ.FreeClosed) :=
    smap_source_l I hZF hw mx my map φ closed ρ η points
  have targetAlphabet : Td_alphabet_d (w 0) (w 1) (w 2) :=
    (td_alphabet_sat_l targetExt η (.bound 0) (.bound 1) (.bound 2)).mp
      ((transfer (td_alphabet_m (.bound 0) (.bound 1) (.bound 2))
        (by simp -implicitDefEqProofs)).mp
          ((td_alphabet_sat_l ext ρ (.bound 0) (.bound 1) (.bound 2)).mpr alphabet))
  -- 不交性量化目标的全部成员，而不只检查旧字母的像。
  let φ : Formula 1 4 := .forallE (.imp (.mem .newest (.bound 2)) (.neg (.mem .newest (.bound 3))))
  have original : Formula.satisfies ρ φ := by
    simp only [φ,Formula.satisfies_forall_iff,Formula.satisfies_imp_iff,
      Formula.satisfies_mem_iff,Formula.satisfies_neg_iff]
    change ∀ x, (smdl_structure_l I (R := R) mx.2.1).mem x (v 1) →
      ¬ (smdl_structure_l I (R := R) mx.2.1).mem x (v 2)
    exact disjoint
  have copied := (transfer φ (by simp -implicitDefEqProofs [φ,Definitional.Formula.FreeClosed])).mp original
  have targetDisjoint : ∀ x, (smdl_structure_l I (R := S) my.2.1).mem x (w 1) →
      ¬ (smdl_structure_l I (R := S) my.2.1).mem x (w 2) := by
    simp only [φ,Formula.satisfies_forall_iff,Formula.satisfies_imp_iff,
      Formula.satisfies_mem_iff,Formula.satisfies_neg_iff] at copied
    change ∀ x, (smdl_structure_l I (R := S) my.2.1).mem x (w 1) →
      ¬ (smdl_structure_l I (R := S) my.2.1).mem x (w 2) at copied
    exact copied
  exact ⟨targetAlphabet,targetDisjoint,
    (map.relation_l I hZF hw mx my (points 3) (points 1)).mp chosen⟩

/-! 若目标侧已经有同一树的 alphabet 证书，则运输得到的字母域由外延性唯一化。
该接口把全图运输和字母唯一性分开，调用方仍必须提供目标侧四点图。 -/
theorem Smap_d.demand_alphabet_unique_l
    (hZF : M.Models ZF) {ω c X R d Y S j : M.Domain}
    (hw : M.IsOmega ω) (mx : Smdl_d I c X R) (my : Smdl_d I d Y S)
    (map : Smap_d I ω c d X Y j)
    (ext : Extensional (smdl_structure_l I (R := R) mx.2.1))
    (targetExt : Extensional (smdl_structure_l I (R := S) my.2.1))
    (v : Fin 4 → (smdl_structure_l I (R := R) mx.2.1).Domain)
    (w : Fin 4 → (smdl_structure_l I (R := S) my.2.1).Domain)
    (points : ∀ i, Rd_entry_d (v i).val (w i).val j)
    (alphabet : Td_alphabet_d (v 0) (v 1) (v 2))
    (disjoint : ∀ x, (smdl_structure_l I (R := R) mx.2.1).mem x (v 1) →
      ¬ (smdl_structure_l I (R := R) mx.2.1).mem x (v 2))
    (chosen : (smdl_structure_l I (R := R) mx.2.1).mem (v 3) (v 1))
    {A B : (smdl_structure_l I (R := S) my.2.1).Domain}
    (target : Td_alphabet_d (w 0) A B) :
    (w 1 = A) ∧ (w 2 = B) ∧
      (smdl_structure_l I (R := S) my.2.1).mem (w 3) A := by
  obtain ⟨transported, _, chosen'⟩ := Smap_d.demand_alphabet_l hZF hw mx my map
    ext v w points alphabet disjoint chosen
  obtain ⟨eqA, eqB⟩ := Td_alphabet_d.ext_l targetExt transported target
  exact ⟨eqA, eqB, eqA ▸ chosen'⟩

/-! 初等图的总性实际产生目标四点，并保留其图成员性与不交性。
源、目标可以是一般关系呈示；字母域始终是原树的最小字母域。 -/
theorem Smap_d.demand_alphabet_image_l
    {ω c d j X R Y S : M.Domain}
    (mx : Smdl_d I c X R) (my : Smdl_d I d Y S)
    (map : Smap_d I ω c d X Y j)
    (hw : M.IsOmega ω)
    (ext : Extensional (smdl_structure_l I (R := R) mx.2.1))
    (v : Fin 4 → (smdl_structure_l I (R := R) mx.2.1).Domain)
    (alphabet : Td_alphabet_d (v 0) (v 1) (v 2))
    (disjoint : ∀ x, (smdl_structure_l I (R := R) mx.2.1).mem x (v 1) →
      ¬ (smdl_structure_l I (R := R) mx.2.1).mem x (v 2))
    (chosen : (smdl_structure_l I (R := R) mx.2.1).mem (v 3) (v 1)) :
    ∃ w : Fin 4 → (smdl_structure_l I (R := S) my.2.1).Domain,
      (∀ i, Rd_entry_d (v i).val (w i).val j) ∧
      Td_alphabet_d (w 0) (w 1) (w 2) ∧
      (∀ x, (smdl_structure_l I (R := S) my.2.1).mem x (w 1) →
        ¬ (smdl_structure_l I (R := S) my.2.1).mem x (w 2)) ∧
      (smdl_structure_l I (R := S) my.2.1).mem (w 3) (w 1) := by
  let w : Fin 4 → (smdl_structure_l I (R := S) my.2.1).Domain := fun i =>
    ⟨Classical.choose (map.1.1.2.2 (v i).val (v i).property),
      (Classical.choose_spec (map.1.1.2.2 (v i).val (v i).property)).1⟩
  have points (i : Fin 4) : Rd_entry_d (v i).val (w i).val j := by
    exact (Classical.choose_spec (map.1.1.2.2 (v i).val (v i).property)).2
  exact ⟨w, points, Smap_d.demand_alphabet_l hZF hw mx my map ext v w points alphabet disjoint chosen⟩

end YesMetaZFC.SetTheory.LargeCardinal
