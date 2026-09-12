import YesMetaZFC.Model.SmallGraph.Sets

/-!
Church 型候选、小观察降解与原小图的忠实嵌入。
记录代数和小图观察给出外延性与旧像的向下封闭；一般集合构造子的注入性、
并集以及完整 ZF 模型尚未证明。
-/

namespace ZFChurch
universe u v w

def D (X : Type u) := {p : X → Prop // ∃ x, ∀ y, p y ↔ y = x}
def pure {X : Type u} (x : X) : D X := ⟨fun y => y = x, x, fun _ => Iff.rfl⟩

theorem exists_pure {X : Type u} (d : D X) : ∃ x, d = pure x := by
  obtain ⟨x, h⟩ := d.2
  exact ⟨x, Subtype.ext (funext (fun y => propext (h y)))⟩

structure Desc (X : Type u) where
  get : D X → X
  pure_eq : ∀ x, get (pure x) = x

def dmap {X : Type u} {Y : Type v} (f : X → Y) (d : D X) : D Y :=
  ⟨fun y => ∃ x, d.1 x ∧ f x = y, by
    obtain ⟨x, rfl⟩ := exists_pure d
    exact ⟨f x, fun y => ⟨fun ⟨z, h, k⟩ => by cases h; exact k.symm,
      fun h => ⟨x, rfl, h.symm⟩⟩⟩⟩

theorem dmap_pure {X : Type u} {Y : Type v} (f : X → Y) (x : X) :
    dmap f (pure x) = pure (f x) := by
  apply Subtype.ext
  funext y
  apply propext
  exact ⟨fun ⟨z, h, k⟩ => by cases h; exact k.symm, fun h => ⟨x, rfl, h.symm⟩⟩

def prop_desc : Desc Prop where
  get d := ∃ p, d.1 p ∧ p
  pure_eq p := propext ⟨fun ⟨q, h, hq⟩ => by cases h; exact hq,
    fun hp => ⟨p, rfl, hp⟩⟩

/-- 谓词函数空间与给定描述完备载体的积，仍有实际的唯一描述消去。 -/
def record_desc {X : Type u} (d : Desc X) : Desc (X × (X → Prop)) where
  get e := (d.get (dmap Prod.fst e), fun x => ∃ p, e.1 p ∧ p.2 x)
  pure_eq p := by
    apply Prod.ext
    · change d.get (dmap Prod.fst (pure p)) = p.1
      rw [dmap_pure, d.pure_eq]
    · funext x
      apply propext
      exact ⟨fun ⟨q, h, hq⟩ => by cases h; exact hq,
        fun hp => ⟨p, rfl, hp⟩⟩

/-- 小性只作为存在性证书保存；映射不读取任何选定呈现。 -/
def Small (X : Type v) :=
  {p : X → Prop // ∃ (I : Type u) (f : I → X), ∀ x, p x ↔ ∃ i, f i = x}

def image {X : Type u} {Y : Type v} (f : X → Y) (p : X → Prop) : Y → Prop :=
  fun y => ∃ x, p x ∧ f x = y

def small_map {X : Type v} {Y : Type w} (f : X → Y) (s : Small.{u,v} X) : Small.{u,w} Y :=
  ⟨image f s.1, by
    obtain ⟨I, g, h⟩ := s.2
    refine ⟨I, f ∘ g, fun y => ?_⟩
    constructor
    · rintro ⟨x, hx, rfl⟩
      obtain ⟨i, rfl⟩ := (h x).mp hx
      exact ⟨i, rfl⟩
    · rintro ⟨i, rfl⟩
      exact ⟨g i, (h (g i)).mpr ⟨i, rfl⟩, rfl⟩⟩

structure Obs where
  X : Type u
  desc : Desc X
  alg : (X → Prop) → X

def C := (o : Obs.{u}) → o.X

def c_desc : Desc C.{u} where
  get d o := o.desc.get (dmap (fun c => c o) d)
  pure_eq c := by
    funext o
    rw [dmap_pure, o.desc.pure_eq]

def sup (s : Small.{u,u+1} C.{u}) : C.{u} :=
  fun o => o.alg (image (fun c => c o) s.1)

inductive Gen : C.{u} → Prop
  | sup (s : Small.{u,u+1} C.{u}) (h : ∀ c, s.1 c → Gen c) : Gen (sup s)

abbrev V := {c : C.{u} // Gen c}

def v_desc : Desc V.{u} where
  get d := ⟨c_desc.get (dmap Subtype.val d), by
    obtain ⟨v, rfl⟩ := exists_pure d
    rw [dmap_pure, c_desc.pure_eq]
    exact v.2⟩
  pure_eq v := Subtype.ext (by simp only [dmap_pure, c_desc.pure_eq])

def v_sup (s : Small.{u,u+1} V.{u}) : V.{u} :=
  ⟨sup (small_map Subtype.val s), Gen.sup _ (fun _ ⟨v, _, e⟩ => e ▸ v.2)⟩

/-- 第二坐标记录恰好一层的输入像，不要求代数在全幂集上单射。 -/
def record (o : Obs.{u}) : Obs.{u} where
  X := o.X × (o.X → Prop)
  desc := record_desc o.desc
  alg p := (o.alg (image Prod.fst p), image Prod.fst p)

theorem natural (o p : Obs.{u}) (f : o.X → p.X)
    (hf : ∀ s, f (o.alg s) = p.alg (image f s))
    {c : C.{u}} (h : Gen c) : f (c o) = c p := by
  induction h with
  | sup s h ih =>
    change f (o.alg (image (fun c => c o) s.1)) = p.alg (image (fun c => c p) s.1)
    rw [hf]
    apply congrArg p.alg
    funext x
    apply propext
    constructor
    · rintro ⟨y, ⟨c, hc, rfl⟩, he⟩
      exact ⟨c, hc, (ih c hc).symm.trans he⟩
    · rintro ⟨c, hc, he⟩
      exact ⟨c o, ⟨c, hc, rfl⟩, (ih c hc).trans he⟩

theorem record_first (o : Obs.{u}) {c : C.{u}} (h : Gen c) : (c (record o)).1 = c o :=
  natural (record o) o Prod.fst (fun _ => rfl) h

/-- 一个实际给定的小观察族可以同时合并；这里没有选择观察的步骤。 -/
def pi_obs {I : Type u} (o : I → Obs.{u}) : Obs.{u} where
  X := ∀ i, (o i).X
  desc := {
    get := fun d i => (o i).desc.get (dmap (fun f => f i) d)
    pure_eq := fun f => funext (fun i => by rw [dmap_pure, (o i).desc.pure_eq]) }
  alg p i := (o i).alg (image (fun f => f i) p)

theorem pi_eval {I : Type u} (o : I → Obs.{u}) {c : C.{u}} (h : Gen c) (i : I) :
    c (pi_obs o) i = c (o i) :=
  natural (pi_obs o) (o i) (fun f => f i) (fun _ => rfl) h

/--
观察闭包不仅给逐观察见证，而且对每个实际小观察族给同一个候选见证。
缺口因而精确落在整个大观察类，而非有限积或已给小积。
-/
theorem joint_profile {I : Type u} (o : I → Obs.{u}) (s : Small.{u,u+1} C.{u})
    (hs : ∀ x, s.1 x → Gen x) {c : C.{u}} (hc : Gen c)
    (h : ∀ p : Obs.{u}, ∃ x, s.1 x ∧ x p = c p) :
    ∃ x, s.1 x ∧ ∀ i, x (o i) = c (o i) := by
  obtain ⟨x, hx, he⟩ := h (pi_obs o)
  exact ⟨x, hx, fun i => (pi_eval o (hs x hx) i).symm.trans
    ((congrFun he i).trans (pi_eval o hc i))⟩

theorem record_second (o : Obs.{u}) (s : Small.{u,u+1} C.{u})
    (h : ∀ c, s.1 c → Gen c) :
    (sup s (record o)).2 = image (fun c => c o) s.1 := by
  funext x
  apply propext
  constructor
  · rintro ⟨y, ⟨c, hc, rfl⟩, he⟩
    exact ⟨c, hc, (record_first o (h c hc)).symm.trans he⟩
  · rintro ⟨c, hc, he⟩
    exact ⟨c (record o), ⟨c, hc, rfl⟩, (record_first o (h c hc)).trans he⟩

/--
构造子等式能推出每个小观察下的完整成员像相等。
剩余缺口是能否由所有这些像等式恢复原来的小谓词相等。
-/
theorem sup_profiles (s t : Small.{u,u+1} C.{u})
    (hs : ∀ c, s.1 c → Gen c) (ht : ∀ c, t.1 c → Gen c)
    (e : sup s = sup t) (o : Obs.{u}) :
    image (fun c => c o) s.1 = image (fun c => c o) t.1 := by
  rw [← record_second o s hs, ← record_second o t ht, e]

theorem sup_iff_profiles (s t : Small.{u,u+1} C.{u})
    (hs : ∀ c, s.1 c → Gen c) (ht : ∀ c, t.1 c → Gen c) :
    sup s = sup t ↔ ∀ o : Obs.{u},
      image (fun c => c o) s.1 = image (fun c => c o) t.1 :=
  ⟨fun e => sup_profiles s t hs ht e,
    fun h => funext (fun o => congrArg o.alg (h o))⟩

/-- 空性观察是实际实例；输入、输出和描述结构均已构造。 -/
def empty_obs : Obs.{0} := ⟨Prop, prop_desc, fun p => ¬ ∃ q, p q⟩

def empty_family : Small.{0,1} C.{0} :=
  ⟨fun _ => False, PEmpty, PEmpty.elim, fun _ => ⟨False.elim,
    fun ⟨i, _⟩ => PEmpty.elim i⟩⟩

def singleton_family (c : C.{0}) : Small.{0,1} C.{0} :=
  ⟨fun x => x = c, PUnit, fun _ => c, fun _ =>
    ⟨fun h => ⟨PUnit.unit, h.symm⟩, fun ⟨_, h⟩ => h.symm⟩⟩

def empty : C.{0} := sup empty_family
def singleton (c : C.{0}) : C.{0} := sup (singleton_family c)

theorem empty_gen : Gen empty := Gen.sup _ (fun _ h => False.elim h)
theorem singleton_gen {c : C.{0}} (h : Gen c) : Gen (singleton c) :=
  Gen.sup _ (fun _ e => e ▸ h)

theorem empty_ne_singleton (c : C.{0}) : empty ≠ singleton c := by
  intro e
  have h : empty empty_obs := fun ⟨_, _, hn, _⟩ => hn
  have k : singleton c empty_obs := Eq.mp (congrArg (fun z => z empty_obs) e) h
  exact k ⟨c empty_obs, c, rfl, rfl⟩

open YesMetaZFC.Model.SmallGraph

def pred_desc (X : Type u) : Desc (X → Prop) where
  get d x := ∃ p, d.1 p ∧ p x
  pure_eq p := funext (fun x => propext
    ⟨fun ⟨q, h, hq⟩ => by cases h; exact hq, fun hp => ⟨p, rfl, hp⟩⟩)

def of_family {I : Type u} (f : I → C.{u}) : Small.{u,u+1} C.{u} :=
  ⟨fun c => ∃ i, f i = c, I, f, fun _ => Iff.rfl⟩

/-- 给定小图的双模拟剖面，是真正的小观察代数。 -/
def graph_obs (G : WF_graph.{u}) : Obs.{u} where
  X := G.Domain → Prop
  desc := pred_desc G.Domain
  alg S a :=
    (∀ p, S p → ∃ b, G.mem b a ∧ p b) ∧
    (∀ b, G.mem b a → ∃ p, S p ∧ p b)

/-- 只有一个给定图，沿其原始小节点直接递归，不收集任选的子图呈现。 -/
def graph_code (G : WF_graph.{u}) : G.Domain → C.{u} :=
  G.wf.fix (fun a f => sup (of_family (fun b : {b // G.mem b a} => f b.1 b.2)))

theorem graph_code_eq (G : WF_graph.{u}) (a : G.Domain) :
    graph_code G a = sup (of_family (fun b : {b // G.mem b a} => graph_code G b.1)) :=
  WellFounded.fix_eq G.wf _ a

theorem graph_code_gen (G : WF_graph.{u}) (a : G.Domain) : Gen (graph_code G a) := by
  apply G.wf.induction a
  intro a ih
  rw [graph_code_eq]
  apply Gen.sup
  rintro c ⟨b, rfl⟩
  exact ih b.1 b.2

theorem graph_code_self (G : WF_graph.{u}) (a : G.Domain) :
    graph_code G a (graph_obs G) a := by
  apply G.wf.induction a
  intro a ih
  rw [graph_code_eq]
  constructor
  · rintro p ⟨c, ⟨b, rfl⟩, rfl⟩
    exact ⟨b.1, b.2, ih b.1 b.2⟩
  · intro b hb
    exact ⟨graph_code G b (graph_obs G),
      ⟨graph_code G b, ⟨⟨b, hb⟩, rfl⟩, rfl⟩, ih b hb⟩

/-- 命中图节点的生成值唯一；归纳逐次使用匹配，不把匹配节点选成函数。 -/
theorem graph_code_unique (G : WF_graph.{u}) {c : C.{u}} (h : Gen c) :
    ∀ a, c (graph_obs G) a → c = graph_code G a := by
  induction h with
  | sup s h ih =>
    intro a ha
    have hl : ∀ d, s.1 d → ∃ b, G.mem b a ∧ d = graph_code G b := by
      intro d hd
      obtain ⟨b, hb, hp⟩ := ha.1 (d (graph_obs G)) ⟨d, hd, rfl⟩
      exact ⟨b, hb, ih d hd b hp⟩
    have hr : ∀ b, G.mem b a → ∃ d, s.1 d ∧ d = graph_code G b := by
      intro b hb
      obtain ⟨p, ⟨d, hd, rfl⟩, hp⟩ := ha.2 b hb
      exact ⟨d, hd, ih d hd b hp⟩
    rw [graph_code_eq]
    funext o
    apply congrArg o.alg
    funext x
    apply propext
    constructor
    · rintro ⟨d, hd, he⟩
      obtain ⟨b, hb, rfl⟩ := hl d hd
      exact ⟨graph_code G b, ⟨⟨b, hb⟩, rfl⟩, he⟩
    · rintro ⟨d, ⟨b, rfl⟩, he⟩
      obtain ⟨d, hd, e⟩ := hr b.1 b.2
      exact ⟨d, hd, (congrArg (fun c => c o) e).trans he⟩

/-- 对每个已经给出的小图值，观察闭包确实反射为原候选中的成员。 -/
theorem graph_closed (G : WF_graph.{u}) (a : G.Domain) (s : Small.{u,u+1} C.{u})
    (hs : ∀ c, s.1 c → Gen c)
    (h : ∀ o : Obs.{u}, ∃ c, s.1 c ∧ c o = graph_code G a o) :
    ∃ c, s.1 c ∧ c = graph_code G a := by
  obtain ⟨c, hc, he⟩ := h (graph_obs G)
  have hp : c (graph_obs G) a := Eq.mpr (congrFun he a) (graph_code_self G a)
  exact ⟨c, hc, graph_code_unique G (hs c hc) a hp⟩

theorem graph_hit_bisim (G H : WF_graph.{u}) (a : G.Domain) (b : H.Domain)
    (h : graph_code H b (graph_obs G) a) :
    (G.at_node a).toSG_graph.Bisim (H.at_node b).toSG_graph := by
  refine ⟨fun a b => graph_code H b (graph_obs G) a, ?_, h⟩
  intro x y hxy
  rw [graph_code_eq] at hxy
  constructor
  · intro x' hx'
    obtain ⟨p, ⟨c, ⟨y', rfl⟩, rfl⟩, hp⟩ := hxy.2 x' hx'
    exact ⟨y'.1, y'.2, hp⟩
  · intro y' hy'
    exact hxy.1 (graph_code H y' (graph_obs G))
      ⟨graph_code H y', ⟨⟨y', hy'⟩, rfl⟩, rfl⟩

theorem graph_bisim_hit (G H : WF_graph.{u}) (R : G.Domain → H.Domain → Prop)
    (hR : SG_graph.BS_rel G.toSG_graph H.toSG_graph R) (a : G.Domain) (b : H.Domain)
    (h : R a b) : graph_code H b (graph_obs G) a := by
  have hh : ∀ b, ∀ a, R a b → graph_code H b (graph_obs G) a := by
    intro b
    apply H.wf.induction b
    intro b ih a hab
    rw [graph_code_eq]
    constructor
    · rintro p ⟨c, ⟨b', rfl⟩, rfl⟩
      obtain ⟨a', ha', hr⟩ := (hR a b hab).2 b'.1 b'.2
      exact ⟨a', ha', ih b'.1 b'.2 a' hr⟩
    · intro a' ha'
      obtain ⟨b', hb', hr⟩ := (hR a b hab).1 a' ha'
      exact ⟨graph_code H b' (graph_obs G),
        ⟨graph_code H b', ⟨⟨b', hb'⟩, rfl⟩, rfl⟩, ih b' hb' a' hr⟩
  exact hh b a h

theorem graph_code_iff (G H : WF_graph.{u}) (a : G.Domain) (b : H.Domain) :
    graph_code G a = graph_code H b ↔
      (G.at_node a).toSG_graph.Bisim (H.at_node b).toSG_graph := by
  constructor
  · intro e
    apply graph_hit_bisim G H a b
    exact Eq.mp (congrFun (congrArg (fun c => c (graph_obs G)) e) a) (graph_code_self G a)
  · rintro ⟨R, hR, h⟩
    exact (graph_code_unique G (graph_code_gen H b) a (graph_bisim_hit G H R hR a b h)).symm

/-- 整个旧小图商载体进入新候选；等同由双模拟精确控制，不取商代表元。 -/
def sg_code : SG_set.{u} → V.{u} :=
  Quotient.lift (fun G => ⟨graph_code G G.root, graph_code_gen G G.root⟩)
    (fun G H h => Subtype.ext ((graph_code_iff G H G.root H.root).mpr h))

theorem sg_code_injective {x y : SG_set.{u}} (h : sg_code x = sg_code y) : x = y := by
  induction x using Quotient.inductionOn with
  | _ G =>
    induction y using Quotient.inductionOn with
    | _ H =>
      exact SG_set.mk_eq.mpr ((graph_code_iff G H G.root H.root).mp (congrArg Subtype.val h))

/-- 由一步记录观察直接给出局部成员关系；尚未宣称它满足其余集合论公理。 -/
def Mem (c d : C.{u}) : Prop := ∀ o : Obs.{u}, (d (record o)).2 (c o)

theorem mem_sup (s : Small.{u,u+1} C.{u}) (hs : ∀ c, s.1 c → Gen c) (c : C.{u}) :
    Mem c (sup s) ↔ ∀ o : Obs.{u}, ∃ x, s.1 x ∧ x o = c o := by
  constructor
  · intro h o
    have k := h o
    rw [record_second o s hs] at k
    exact k
  · intro h o
    rw [record_second o s hs]
    exact h o

theorem mem_ext {c d : C.{u}} (hc : Gen c) (hd : Gen d)
    (h : ∀ x, Gen x → (Mem x c ↔ Mem x d)) : c = d := by
  cases hc with
  | sup s hs =>
    cases hd with
    | sup t ht =>
      apply (sup_iff_profiles s t hs ht).mpr
      intro o
      funext y
      apply propext
      constructor
      · rintro ⟨x, hx, rfl⟩
        have k : Mem x (sup s) := (mem_sup s hs x).mpr (fun _ => ⟨x, hx, rfl⟩)
        exact (mem_sup t ht x).mp ((h x (hs x hx)).mp k) o
      · rintro ⟨x, hx, rfl⟩
        have k : Mem x (sup t) := (mem_sup t ht x).mpr (fun _ => ⟨x, hx, rfl⟩)
        exact (mem_sup s hs x).mp ((h x (ht x hx)).mpr k) o

/-- 每个旧图值的所有局部成员仍是该图的某个孩子，没有增加新成员。 -/
theorem mem_graph_iff (G : WF_graph.{u}) (a : G.Domain) {c : C.{u}} (hc : Gen c) :
    Mem c (graph_code G a) ↔ ∃ b, G.mem b a ∧ c = graph_code G b := by
  rw [graph_code_eq]
  let f := fun b : {b // G.mem b a} => graph_code G b.1
  have hs : ∀ x, (of_family f).1 x → Gen x := by
    rintro x ⟨b, rfl⟩
    exact graph_code_gen G b.1
  rw [mem_sup (of_family f) hs]
  constructor
  · intro h
    obtain ⟨x, ⟨b, rfl⟩, he⟩ := h (graph_obs G)
    have hp : c (graph_obs G) b.1 := Eq.mp (congrFun he b.1) (graph_code_self G b.1)
    exact ⟨b.1, b.2, graph_code_unique G hc b.1 hp⟩
  · rintro ⟨b, hb, rfl⟩ o
    exact ⟨graph_code G b, ⟨⟨b, hb⟩, rfl⟩, rfl⟩

/-- 旧载体的注入也精确保留和反射原成员关系。 -/
theorem sg_code_mem (x y : SG_set.{u}) :
    Mem (sg_code x).1 (sg_code y).1 ↔ x ∈ y := by
  induction x using Quotient.inductionOn with
  | _ G =>
    induction y using Quotient.inductionOn with
    | _ H =>
      change Mem (graph_code G G.root) (graph_code H H.root) ↔ G.toSG_graph.Raw_mem H.toSG_graph
      rw [mem_graph_iff H H.root (graph_code_gen G G.root)]
      exact ⟨fun ⟨b, hb, e⟩ => ⟨b, hb, (graph_code_iff G H G.root b).mp e⟩,
        fun ⟨b, hb, e⟩ => ⟨b, hb, (graph_code_iff G H G.root b).mpr e⟩⟩

#print axioms record_desc
#print axioms c_desc
#print axioms v_desc
#print axioms v_sup
#print axioms record_first
#print axioms joint_profile
#print axioms sup_profiles
#print axioms sup_iff_profiles
#print axioms empty_ne_singleton
#print axioms graph_code
#print axioms graph_code_unique
#print axioms graph_closed
#print axioms sg_code
#print axioms sg_code_injective
#print axioms mem_ext
#print axioms mem_graph_iff
#print axioms sg_code_mem

end ZFChurch
