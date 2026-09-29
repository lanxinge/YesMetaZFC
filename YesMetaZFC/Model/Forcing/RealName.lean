import YesMetaZFC.Model.Forcing.Valuation
import YesMetaZFC.Model.SmallGraph.Infinity

/-! # 自然数子集的实际名称

复用已有 ω 图：有限序数内部边标记一个被接受的值 t，根到第 n 个有限序数的
边标记 w(n)。布尔滤子调用时取 t = ⊤；构造本身不要求布尔代数运算。
-/

namespace YesMetaZFC.Model.Forcing
open Boolean SmallGraph
universe u v
variable {B : Type v}

def nat_set_l (n : Nat) : SG_set.{u} := SG_set.omega_piece (List.replicate n PUnit.unit)

theorem nat_set_injective_l {m n : Nat} (h : nat_set_l.{u} m = nat_set_l n) : m = n := by
  have hn (x : SG_set.{u}) : ¬ x ∈ x := by
    induction x using SG_set.mem_wf.induction with
    | h x ih => exact fun hx => ih x hx hx
  have hm {i j : Nat} (hij : i < j) : nat_set_l.{u} i ∈ nat_set_l j :=
    (SG_set.omega_piece_mem _ _).mpr ⟨List.replicate i PUnit.unit, by simpa using hij, rfl⟩
  apply Nat.le_antisymm <;> apply Nat.le_of_not_gt <;> intro k
  · have hk := hm k
    rw [h] at hk
    exact hn _ hk
  · have hk := hm k
    rw [h] at hk
    exact hn _ hk

def real_name_l (t : B) (w : Nat → B) : BV_graph.{u, v} B where
  toWF_graph := omega_graph
  val a b := match a, b with
    | some a, none => w a.length
    | _, _ => t

/-- 有限观察根以下的边全为顶值，求值仍是同一个有限序数。 -/
theorem val_real_node_l (t : B) (U : B → Prop) (h : U t)
    (w : Nat → B) (a : List PUnit.{u+1}) :
    val_l U ((real_name_l t w).at_node (some a)) = SG_set.omega_piece a := by
  apply SG_set.mk_eq.mpr
  refine ⟨fun b c => ∃ l, b = some l ∧ c = some l, ?_, ⟨a, rfl, rfl⟩⟩
  rintro b c ⟨l, rfl, rfl⟩
  constructor
  · rintro b ⟨hb, _⟩
    cases b with
    | none => exact hb.elim
    | some k => exact ⟨some k, hb, k, rfl, rfl⟩
  · intro c hc
    cases c with
    | none => exact hc.elim
    | some k => exact ⟨some k, ⟨hc, h⟩, k, rfl, rfl⟩

theorem val_real_mem_l (t : B) (U : B → Prop) (h : U t)
    (w : Nat → B) (x : SG_set.{u}) :
    x ∈ val_l U (real_name_l t w) ↔ ∃ n, U (w n) ∧ x = nat_set_l n := by
  rw [val_mem_l]
  constructor
  · rintro ⟨⟨a, ha⟩, hw, hx⟩
    cases a with
    | none => exact ha.elim
    | some a =>
      refine ⟨a.length, hw, hx.trans ((val_real_node_l t U h w a).trans ?_)⟩
      exact SG_set.omega_piece_congr (by simp)
  · rintro ⟨n, hn, rfl⟩
    refine ⟨⟨some (List.replicate n PUnit.unit), trivial⟩, ?_, ?_⟩
    · simpa only [real_name_l, omega_graph, List.length_replicate] using hn
    · exact (val_real_node_l t U h w _).symm

def real_graph_l (r : Nat → Prop) : WF_graph.{u} :=
  val_graph_l id (real_name_l True r)

def real_set_l (r : Nat → Prop) : SG_set.{u} := SG_set.mk (real_graph_l r)

theorem real_mem_l (r : Nat → Prop) (x : SG_set.{u}) :
    x ∈ real_set_l r ↔ ∃ n, r n ∧ x = nat_set_l n :=
  val_real_mem_l True id trivial r x

theorem nat_mem_real_l (r : Nat → Prop) (n : Nat) : nat_set_l.{u} n ∈ real_set_l r ↔ r n :=
  (real_mem_l r _).trans ⟨fun ⟨_, hm, e⟩ => nat_set_injective_l e ▸ hm,
    fun h => ⟨n, h, rfl⟩⟩

theorem val_real_l (t : B) (U : B → Prop) (h : U t) (w : Nat → B) :
    val_l U (real_name_l.{u, v} t w) = real_set_l (fun n => U (w n)) :=
  SG_set.ext fun x => (val_real_mem_l t U h w x).trans (real_mem_l _ x).symm

theorem real_subset_omega_l (r : Nat → Prop) {x : SG_set.{u}} (h : x ∈ real_set_l r) :
    x ∈ SG_set.omega := by
  obtain ⟨n, _, rfl⟩ := (real_mem_l r x).mp h
  exact (SG_set.mem_mk omega_graph _).mpr ⟨some (List.replicate n PUnit.unit), trivial, rfl⟩

/-- ω 图的显式枚举也枚举上面全部实数名称和规范实数名称的节点。 -/
def omega_enum_l : Nat → omega_graph.{u}.Domain
  | 0 => none
  | n+1 => some (List.replicate n PUnit.unit)

theorem omega_enum_surjective_l (a : omega_graph.{u}.Domain) : ∃ n, omega_enum_l n = a := by
  cases a with
  | none => exact ⟨0, rfl⟩
  | some a =>
    refine ⟨a.length+1, congrArg some ?_⟩
    exact (List.eq_replicate_of_mem (fun b _ => Subsingleton.elim b PUnit.unit)).symm

end YesMetaZFC.Model.Forcing
