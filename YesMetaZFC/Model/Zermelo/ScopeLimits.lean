import YesMetaZFC.Model.Zermelo.Collection
import YesMetaZFC.Model.Zermelo.Model

/-! # 有限次幂集扩张不能承载统一重放
旧载体 D 是传递集。每个后继范围 D∪P(D) 中的对象都是 D 的子集，
所以虽然 D 已成为新范围中的对象，新范围内却没有任何对象以 D 为成员。
这直接否定原配对公理的统一范围解释；有限次迭代始终重现同一个障碍。
本结论只排除统一范围重放，并不排除保留不同量词范围的证明处理。
-/

namespace YesMetaZFC.Model.Zermelo
open Logic Logic.FirstOrder SetTheory SetTheory.Definitional
universe u
attribute [local implicit_reducible] SetTheory.signature

abbrev Sl_trans (d : V.{u}) : Prop := ∀ x, x ∈ d → V.sub x d

theorem sl_irrefl (d : V.{u}) : ¬ d ∈ d :=
  V.mem_ind (p := fun x => ¬ x ∈ x) (fun x ih h => ih x h h) d

/-- 升层后，旧载体是实际的传递集合。 -/
theorem sl_space_trans : Sl_trans gl_space.{u} := by
  intro a ha x hx
  exact st_use ha (fun ⟨b, e⟩ => st_use (gl_member b ((V.mem_right e).mp hx))
    (fun ⟨y, _, h⟩ => (V.mem_left h).mpr (V.elem_mem gl_space y)))

/-- 后继层的每一个对象，其全部成员仍在前一层。 -/
theorem sl_next_sub (d : V.{u}) (h : Sl_trans d) {x : V.{u}} (hx : x ∈ sc_next d) :
    V.sub x d :=
  st_use ((V.union_mem _ _).mp hx) (fun ⟨_a, ha, hx⟩ =>
    st_use ((V.pair_mem _ _ _).mp ha) (fun e => e.elim
      (fun e => h x ((V.mem_right e).mp hx))
      (fun e => (V.power_mem d x).mp ((V.mem_right e).mp hx))))

theorem sl_next_trans (d : V.{u}) (h : Sl_trans d) : Sl_trans (sc_next d) :=
  fun _x hx y hy => (sc_bounds d).1 y (sl_next_sub d h hx y hy)

theorem sl_self_next (d : V.{u}) : d ∈ sc_next d :=
  (sc_bounds d).2 d ((V.power_mem d d).mpr (fun _ => id))

/-- 反例直接使用原配对公理，而不是另造一个配对模式。 -/
theorem sl_pair_fail (d : V.{u}) (h : Sl_trans d) (ρ : Env.{u} [] []) :
    ¬ sc_sat (Project.fo_sentence Axioms.pairing) (sc_next d) ρ := by
  intro p
  have hd := sl_self_next d
  exact st_use (p d hd d hd) (fun ⟨c, hc, q⟩ => sl_irrefl d
    (sl_next_sub d h hc d ((q d hd).mpr (nn_in (.inl (V.eq_refl d))))))

def sl_stage (d : V.{u}) : Nat → V.{u}
  | 0 => d
  | n+1 => sc_next (sl_stage d n)

theorem sl_stage_trans (d : V.{u}) (h : Sl_trans d) : ∀ n, Sl_trans (sl_stage d n)
  | 0 => h
  | n+1 => sl_next_trans _ (sl_stage_trans d h n)

/-- 原配对公理在旧载体上成立。 -/
theorem sl_pair_seed (ρ : Env.{u} [] []) :
    sc_sat (Project.fo_sentence Axioms.pairing) gl_space (gl_env ρ) :=
  (gl_sat _ ρ).mpr (models_z _ ⟨Axioms.pairing, Z.Axiom.pairing, rfl⟩ ρ)

/-- 无论有限迭代多少次，每个真正扩张后的阶段都不满足统一配对。 -/
theorem sl_pair_stage (n : Nat) (ρ : Env.{u+1} [] []) :
    ¬ sc_sat (Project.fo_sentence Axioms.pairing) (sl_stage gl_space.{u} (n+1)) ρ :=
  sl_pair_fail _ (sl_stage_trans _ sl_space_trans n) ρ

/-- 非空输入上的恒真关系，按现有“保留全部见证”构造得到整个旧载体。 -/
def sl_pool : V.{u+1} :=
  gl_pool (.truth : FirstOrder.Formula ℒ [] [.set, .set]) FirstOrder.Env.empty
    (V.pair V.empty.{u} V.empty)

theorem sl_pool_eq : V.eq sl_pool.{u} gl_space :=
  V.ext (fun y => (gl_pool_mem .truth FirstOrder.Env.empty (V.pair V.empty V.empty) y).trans
    ⟨And.left, fun hy => ⟨hy, nn_in ⟨gl_lift V.empty,
      (gl_mem _ _).mpr ((V.pair_mem _ _ _).mpr (nn_in (.inl (V.eq_refl _)))), trivial⟩⟩⟩)

/-- 任何有限阶段都不能同时容纳这个实际收集输出，并保有原配对公理。 -/
theorem sl_no_uniform (ρ : Env.{u+1} [] []) :
    ¬∃ n, sl_pool.{u} ∈ sl_stage gl_space n ∧
      sc_sat (Project.fo_sentence Axioms.pairing) (sl_stage gl_space n) ρ := by
  rintro ⟨n, hc, hp⟩
  cases n with
  | zero => exact sl_irrefl gl_space ((V.mem_left sl_pool_eq).mp hc)
  | succ n => exact sl_pair_stage n ρ hp

/-- info: 'YesMetaZFC.Model.Zermelo.sl_pair_seed' does not depend on any axioms -/
#guard_msgs in
#print axioms sl_pair_seed
/-- info: 'YesMetaZFC.Model.Zermelo.sl_no_uniform' does not depend on any axioms -/
#guard_msgs in
#print axioms sl_no_uniform
end YesMetaZFC.Model.Zermelo
