import YesMetaZFC.Model.Forcing.Applications.Cohen.Algebra
import YesMetaZFC.Model.Forcing.External.RealName
import YesMetaZFC.Model.Forcing.External.Extension
import YesMetaZFC.Model.Forcing.External.NameGeneric

/-! # Cohen 名称及可数旧实数族之外的新实数

第 n 位的布尔值由“该位已取 true”的条件正则化得到。每个旧实数都给出一个
明确稠密开集，要求在某一位与它不同；同时允许指定任意额外可数稠密族。
-/

namespace YesMetaZFC.Model.Forcing
open Boolean SmallGraph

private abbrev R := (tree_order_l Bool).toPO_pre

private theorem bit_lower_l (n : Nat) (b : Bool) : R.Lower_l (fun p => p[n]? = some b) := by
  rintro p q ⟨s, rfl⟩ h
  obtain ⟨hn, _⟩ := List.getElem?_eq_some_iff.mp h
  rwa [List.getElem?_append_left hn]

def cohen_bit_l (n : Nat) : Cohen_l := R.ro_regularize_l (fun p => p[n]? = some true)

theorem cohen_bit_true_l (p : List Bool) :
    cohen_algebra_l.le (R.ro_principal_l (p ++ [true])) (cohen_bit_l p.length) :=
  (R.ro_principal_le_iff_l _ _).mpr
    (R.ro_reg_intro_l (bit_lower_l _ _) (by simp))

theorem cohen_bit_false_l (p : List Bool) :
    cohen_algebra_l.le (R.ro_principal_l (p ++ [false]))
      (cohen_algebra_l.neg (cohen_bit_l p.length)) := by
  apply (R.ro_principal_le_iff_l _ _).mpr
  intro q hq hb
  have hfalse : q[p.length]? = some false :=
    bit_lower_l _ _ hq (by simp)
  exact hb q (R.le_refl _) (fun r hr ht => by
    have hf : r[p.length]? = some false := bit_lower_l _ _ hr hfalse
    rw [ht] at hf
    cases hf)

def cohen_real_name_l : BV_graph.{0, 0} Cohen_l :=
  real_name_l cohen_algebra_l.top cohen_bit_l

/-- 与指定旧实数在某一位已经确定地不同。 -/
def cohen_avoid_l (r : Nat → Prop) (p : Pos_l cohen_algebra_l.toBA_alg) : Prop :=
  ∃ n, (r n ∧ cohen_algebra_l.le p.1 (cohen_algebra_l.neg (cohen_bit_l n))) ∨
    (¬ r n ∧ cohen_algebra_l.le p.1 (cohen_bit_l n))

theorem cohen_avoid_lower_l (r : Nat → Prop) :
    (positive_order_l cohen_algebra_l.toBA_alg).toPO_pre.Lower_l (cohen_avoid_l r) := by
  rintro p q h ⟨n, hn | hn⟩
  · exact ⟨n, Or.inl ⟨hn.1, cohen_algebra_l.le_trans h hn.2⟩⟩
  · exact ⟨n, Or.inr ⟨hn.1, cohen_algebra_l.le_trans h hn.2⟩⟩

theorem cohen_avoid_dense_l (r : Nat → Prop) :
    (positive_order_l cohen_algebra_l.toBA_alg).toPO_pre.Dense_l (cohen_avoid_l r) := by
  intro p
  obtain ⟨q, hq⟩ := R.ro_dense_l.dense p
  rcases Classical.em (r q.length) with h | h
  · exact ⟨R.ro_condition_l (q ++ [false]),
      cohen_algebra_l.le_trans (R.ro_principal_mono_l (List.prefix_append _ _)) hq,
      q.length, Or.inl ⟨h, cohen_bit_false_l q⟩⟩
  · exact ⟨R.ro_condition_l (q ++ [true]),
      cohen_algebra_l.le_trans (R.ro_principal_mono_l (List.prefix_append _ _)) hq,
      q.length, Or.inr ⟨h, cohen_bit_true_l q⟩⟩

theorem cohen_val_l (U : Filter_l cohen_algebra_l.toBA_alg) :
    val_l U.mem cohen_real_name_l = real_set_l (fun n => U.mem (cohen_bit_l n)) :=
  val_real_l cohen_algebra_l.top U.mem U.top_mem cohen_bit_l

theorem cohen_fresh_l (U : Filter_l cohen_algebra_l.toBA_alg) (hU : U.Proper_l)
    (r : Nat → Prop) (h : BF_meets_l U (cohen_avoid_l r)) :
    val_l U.mem cohen_real_name_l ≠ real_set_l r := by
  intro e
  rw [cohen_val_l] at e
  have he n : U.mem (cohen_bit_l n) ↔ r n := by
    rw [← nat_mem_real_l.{0} (fun k => U.mem (cohen_bit_l k)) n, e, nat_mem_real_l]
  obtain ⟨p, hp, n, hn | hn⟩ := h
  · exact U.not_neg_l hU ((he n).mpr hn.1) (U.upward hp hn.2)
  · exact hn.1 ((he n).mp (U.upward hp hn.2))

def cohen_family_l (r : Nat → Nat → Prop) : Nat → BV_graph.{0, 0} Cohen_l
  | 0 => BV_graph.empty cohen_algebra_l.toPO_bot
  | 1 => cohen_real_name_l
  | 2 => check_graph_l cohen_algebra_l.toBA_alg omega_graph
  | n+3 => check_graph_l cohen_algebra_l.toBA_alg (real_graph_l (r n))

def cohen_node_enum_l (r : Nat → Nat → Prop) : ∀ i, Nat → (cohen_family_l r i).Domain
  | 0, _ => PUnit.unit
  | 1, n => omega_enum_l n
  | 2, n => omega_enum_l n
  | _+3, n => omega_enum_l n

theorem cohen_node_surjective_l (r : Nat → Nat → Prop)
    (i : Nat) (a : (cohen_family_l r i).Domain) : ∃ n, cohen_node_enum_l r i n = a := by
  cases i with
  | zero =>
    change PUnit at a
    cases a
    exact ⟨0, rfl⟩
  | succ i =>
    cases i with
    | zero => exact omega_enum_surjective_l a
    | succ i => cases i <;> exact omega_enum_surjective_l a

/-- ω、旧实数的规范名称与 Cohen 名称共同生成一个实际子名称封闭域。 -/
def cohen_names_l (r : Nat → Nat → Prop) : Name_domain_l.{0, 0} Cohen_l :=
  name_span_l cohen_algebra_l.toBA_alg (fun G => ∃ i, cohen_family_l r i = G)

theorem cohen_ext_old_l (r : Nat → Nat → Prop) (U : Filter_l cohen_algebra_l.toBA_alg)
    (n : Nat) : Ext_l (cohen_names_l r) U.mem (real_set_l (r n)) :=
  ext_check_l cohen_algebra_l.toBA_alg _ U (real_graph_l (r n))
    (name_span_mem_l _ ⟨n+3, rfl⟩)

theorem cohen_ext_omega_l (r : Nat → Nat → Prop) (U : Filter_l cohen_algebra_l.toBA_alg) :
    Ext_l (cohen_names_l r) U.mem SG_set.omega :=
  ext_check_l cohen_algebra_l.toBA_alg _ U omega_graph (name_span_mem_l _ ⟨2, rfl⟩)

theorem cohen_ext_new_l (r : Nat → Nat → Prop) (U : Filter_l cohen_algebra_l.toBA_alg) :
    Ext_l (cohen_names_l r) U.mem (val_l U.mem cohen_real_name_l) :=
  ext_val_l _ _ (name_span_mem_l _ ⟨1, rfl⟩)

/-- 可数种子族的节点要求已经覆盖其整个子名称封闭域。 -/
theorem cohen_names_generic_l (r : Nat → Nat → Prop)
    (U : Filter_l cohen_algebra_l.toBA_alg)
    (h : ∀ i j, Name_generic_l cohen_algebra_l U (cohen_family_l r i) (cohen_family_l r j))
    (G H : BV_graph.{0, 0} Cohen_l) (hG : (cohen_names_l r).mem G)
    (hH : (cohen_names_l r).mem H) : Name_generic_l cohen_algebra_l U G H := by
  have hn K (hK : (cohen_names_l r).mem K) : ∃ i a, K = (cohen_family_l r i).at_node a := by
    rcases hK with rfl | ⟨_, ⟨i, rfl⟩, a, rfl⟩
    · exact ⟨0, PUnit.unit, rfl⟩
    · exact ⟨i, a, rfl⟩
  obtain ⟨i, _, rfl⟩ := hn G hG
  obtain ⟨j, _, rfl⟩ := hn H hH
  exact h i j

/-- 同时完成泛型滤子、新实数及整个实际名称域的原子真值要求。 -/
theorem cohen_extension_l (r : Nat → Nat → Prop)
    (D : Nat → Pos_l cohen_algebra_l.toBA_alg → Prop)
    (hD : ∀ n, (positive_order_l cohen_algebra_l.toBA_alg).toPO_pre.Dense_l (D n))
    (p : Pos_l cohen_algebra_l.toBA_alg) :
    ∃ U : Filter_l cohen_algebra_l.toBA_alg, U.Maximal_l ∧ U.mem p.1 ∧
      (∀ n, BF_meets_l U (D n)) ∧
      (∀ n, val_l U.mem cohen_real_name_l ≠ real_set_l (r n)) ∧
      ∀ G H, (cohen_names_l r).mem G → (cohen_names_l r).mem H →
        Name_generic_l cohen_algebra_l U G H := by
  obtain ⟨U, hU, hp, h, hg⟩ := name_family_generic_l cohen_algebra_l
    (cohen_family_l r) (cohen_node_enum_l r) (cohen_node_surjective_l r)
    (fun n q => cohen_avoid_l (r n) q ∧ D n q)
    (fun n => (positive_order_l cohen_algebra_l.toBA_alg).toPO_pre.dense_inter_l
      (cohen_avoid_dense_l (r n)) (hD n) (cohen_avoid_lower_l (r n))) p
  refine ⟨U, hU, hp, fun n => ?_, fun n => ?_, cohen_names_generic_l r U hg⟩
  · obtain ⟨q, hq, _, hd⟩ := h n
    exact ⟨q, hq, hd⟩
  · obtain ⟨q, hq, ha, _⟩ := h n
    exact cohen_fresh_l U hU.1 (r n) ⟨q, hq, ha⟩

end YesMetaZFC.Model.Forcing
