import YesMetaZFC.Model.Forcing.Applications.Cohen.Real
import YesMetaZFC.Model.Forcing.External.FormulaEnumeration
import YesMetaZFC.Model.Forcing.External.ZFCBase

/-! # Cohen 扩张中全公式真值的自动装配

同一滤子处理指定的可数公式与赋值族、原子要求、额外稠密族和旧实数规避要求。
量词证书由公式递归生成。这里尚不声称生成名称域对全部 ZFC 集合操作封闭。
-/

namespace YesMetaZFC.Model.Forcing
open Boolean Logic Logic.FirstOrder

/-- 一次调用生成实际扩张，并自动证明所给每个公式实例的完整真值对应。 -/
theorem cohen_formula_extension_l (r : Nat → Nat → Prop)
    (Q : Nat → Fm_query_l cohen_algebra_l (cohen_names_l r))
    (D : Nat → Pos_l cohen_algebra_l.toBA_alg → Prop)
    (hD : ∀ n, (positive_order_l cohen_algebra_l.toBA_alg).toPO_pre.Dense_l (D n))
    (p : Pos_l cohen_algebra_l.toBA_alg) :
    ∃ U : Filter_l cohen_algebra_l.toBA_alg, U.Maximal_l ∧ U.mem p.1 ∧
      (∀ n, BF_meets_l U (D n)) ∧
      (∀ n, val_l U.mem cohen_real_name_l ≠ real_set_l (r n)) ∧
      ∀ n, U.mem (BV_str.value cohen_algebra_l (domain_str_l cohen_algebra_l (cohen_names_l r))
        (Q n).formula (Q n).env) ↔
        (Q n).formula.satisfies ((Q n).env.map
          (val_map_l cohen_algebra_l (cohen_names_l r) U.mem).map) := by
  let N := cohen_names_l r
  let R := (positive_order_l cohen_algebra_l.toBA_alg).toPO_pre
  let e := span_enum_l cohen_algebra_l (cohen_family_l r) (cohen_node_enum_l r)
  have he : Function.Surjective e := span_enum_surjective_l cohen_algebra_l
    (cohen_family_l r) (cohen_node_enum_l r) (cohen_node_surjective_l r)
  let E n q := fm_dense_l cohen_algebra_l N e (Q (NatPairing.first n)).formula
    (Q (NatPairing.first n)).env (NatPairing.second n) q ∧ D (NatPairing.first n) q
  have hE n : R.Dense_l (E n) := R.dense_inter_l
    (fm_dense_dense_l cohen_algebra_l N e _ _ _) (hD _)
    (fm_dense_lower_l cohen_algebra_l N e _ _ _)
  obtain ⟨U, hU, hp, h, hn, hg⟩ := cohen_extension_l r E hE p
  refine ⟨U, hU, hp, fun n => ?_, hn, fun n => ?_⟩
  · obtain ⟨q, hq, _, hd⟩ := h (NatPairing.pair n 0)
    exact ⟨q, hq, by simpa only [NatPairing.first_pair] using hd⟩
  · apply val_formula_iff_l cohen_algebra_l N U hU hg
    apply fm_generic_of_meets_l cohen_algebra_l N e he U
    intro k
    obtain ⟨q, hq, hφ, _⟩ := h (NatPairing.pair n k)
    have hc := congrArg (fun i : Nat × Nat =>
      fm_dense_l cohen_algebra_l N e (Q i.1).formula (Q i.1).env i.2 q)
      (show (NatPairing.first (NatPairing.pair n k), NatPairing.second (NatPairing.pair n k)) = (n, k)
        from Prod.ext (NatPairing.first_pair n k) (NatPairing.second_pair n k))
    exact ⟨q, hq, Eq.mp hc hφ⟩

/-- 全部原一阶公式和有限参数同时满足真值对应；公式调度在内部自动生成。 -/
theorem cohen_full_extension_l (r : Nat → Nat → Prop)
    (D : Nat → Pos_l cohen_algebra_l.toBA_alg → Prop)
    (hD : ∀ n, (positive_order_l cohen_algebra_l.toBA_alg).toPO_pre.Dense_l (D n))
    (p : Pos_l cohen_algebra_l.toBA_alg) :
    ∃ U : Filter_l cohen_algebra_l.toBA_alg, U.Maximal_l ∧ U.mem p.1 ∧
      (∀ n, BF_meets_l U (D n)) ∧
      (∀ n, val_l U.mem cohen_real_name_l ≠ real_set_l (r n)) ∧
      ∀ {b f} (φ : Formula ℒ b f)
        (ρ : (domain_str_l cohen_algebra_l (cohen_names_l r)).Env cohen_algebra_l.toBA_alg b f),
        U.mem (BV_str.value cohen_algebra_l (domain_str_l cohen_algebra_l (cohen_names_l r)) φ ρ) ↔
          φ.satisfies (ρ.map (val_map_l cohen_algebra_l (cohen_names_l r) U.mem).map) := by
  let N := cohen_names_l r
  let e := span_enum_l cohen_algebra_l (cohen_family_l r) (cohen_node_enum_l r)
  obtain ⟨Q, hQ⟩ := fm_query_enumeration_l cohen_algebra_l N e
    (span_enum_surjective_l cohen_algebra_l _ _ (cohen_node_surjective_l r))
  obtain ⟨U, hU, hp, hd, hn, h⟩ := cohen_formula_extension_l r Q D hD p
  refine ⟨U, hU, hp, hd, hn, fun {b f} φ ρ => ?_⟩
  obtain ⟨i, hi⟩ := hQ ⟨b, f, φ, ρ⟩
  -- 公式与赋值按同一条查询搬运，始终保留它们共同的依赖上下文。
  have ht := congrArg (fun q : Fm_query_l cohen_algebra_l N =>
    U.mem (BV_str.value cohen_algebra_l (domain_str_l cohen_algebra_l N) q.formula q.env) ↔
      q.formula.satisfies (q.env.map (val_map_l cohen_algebra_l N U.mem).map)) hi
  exact Eq.mp ht (h i)

/-- 当前实际名称域已保持的四条原 ZFC 公理；无穷见证固定为已有 ω。 -/
theorem cohen_zfc_base_l (r : Nat → Nat → Prop) (U : Filter_l cohen_algebra_l.toBA_alg) :
    (ext_structure_l (cohen_names_l r) U.mem).SatisfiesSentence SetTheory.Axioms.extensionality ∧
    (ext_structure_l (cohen_names_l r) U.mem).SatisfiesSentence SetTheory.Axioms.emptySet ∧
    (ext_structure_l (cohen_names_l r) U.mem).SatisfiesSentence SetTheory.Axioms.foundation ∧
    (ext_structure_l (cohen_names_l r) U.mem).SatisfiesSentence SetTheory.Axioms.infinity := by
  obtain ⟨he, hz, hf⟩ := ext_zfc_base_l (cohen_names_l r) U.mem
  exact ⟨he, hz, hf, ext_zfc_infinity_l _ _ (cohen_ext_omega_l r U)⟩

end YesMetaZFC.Model.Forcing
