import YesMetaZFC.SetTheory.LargeCardinal.Iteration.CountableLimit
import YesMetaZFC.SetTheory.Ord.Code.NaturalBound

/-! # 奇祖先深度上的内部调度

深度 d 的表以 d × ω 为定义域，保存各祖先枚举行在当前模型中的像。
后继追加父节点的枚举行，再沿本次原边逐值运输。调度只读取深度，
不读取全局轮号；全部函数都是背景模型中的实际集合。
-/
namespace YesMetaZFC.SetTheory.LargeCardinal
open Definitional.Project InnerModel Internal
universe u
variable {M : Structure.{u}}

structure Td_enum_d (Ω X R U E : M.Domain) : Prop where
  function : Fn0_d Ω X E
  letters : ∀ n x, Rd_entry_d n x E → Rd_entry_d x U R
  onto : ∀ x, M.mem x X → Rd_entry_d x U R → ∃ n, M.mem n Ω ∧ Rd_entry_d n x E

structure Td_depth_d (I : kpair_convention_l.Interpretation M)
    (Ω X R U d F : M.Domain) : Prop where
  natural : M.mem d Ω
  table : ∃ D, M.IsCartesianProduct I D d Ω ∧ Fn0_d D X F
  letters : ∀ p x, Rd_entry_d p x F → Rd_entry_d x U R

/-- 深度 d+1 服务代码 d；零深度及配对像外的深度不提出任务。 -/
def Td_pick_d (I : kpair_convention_l.Interpretation M) (Ω d F z : M.Domain) : Prop :=
  ∀ n i e p, M.SuccessorOf d n → M.mem i Ω → M.mem e Ω →
    Oc_pair_d I i e n → KPair_d M p i e → Rd_entry_d p z F

/-- 新表的每项只来自旧表或父节点本身的枚举行，并使用同一实际原边。 -/
def Td_depth_next_d (Ω d F E j p y : M.Domain) : Prop :=
  ∃ i e x, KPair_d M p i e ∧ M.mem e Ω ∧
    ((M.mem i d ∧ Rd_entry_d p x F) ∨ (i = d ∧ Rd_entry_d e x E)) ∧ Rd_entry_d x y j

def td_depth_next_m {n} (Ω d F E j p y : Term n) : Formula 1 n := set[n] ⟪
  ∃ i e x, ⌜kpair0_m⌝ₚ(⌜p⌝ₛ,i,e) ∧ e ∈ ⌜Ω⌝ₛ ∧
    ((i ∈ ⌜d⌝ₛ ∧ ⌜rd_entry0_m⌝ₚ(⌜p⌝ₛ,x,⌜F⌝ₛ)) ∨
      (i = ⌜d⌝ₛ ∧ ⌜rd_entry0_m⌝ₚ(e,x,⌜E⌝ₛ))) ∧
    ⌜rd_entry0_m⌝ₚ(x,⌜y⌝ₛ,⌜j⌝ₛ)⟫
derive_free_closed td_depth_next_m

theorem td_depth_next_sat_l (hE : Extensional M) {n} (ρ : Env M n)
    (Ω d F E j p y : Term n) :
    Formula.satisfies ρ (td_depth_next_m Ω d F E j p y) ↔
      Td_depth_next_d (Ω.eval ρ) (d.eval ρ) (F.eval ρ) (E.eval ρ) (j.eval ρ)
        (p.eval ρ) (y.eval ρ) := by
  simp only [td_depth_next_m,Td_depth_next_d,Formula.satisfies_exists_iff,
    Formula.satisfies_conj_iff,Formula.satisfies_disj_iff,Formula.satisfies_mem_iff,
    Formula.satisfies_extensionalEq_iff_eq hE,kpair0_sat_l hE,rd_entry0_sat_l hE,
    Definitional.Term.eval_weaken]
  rfl

variable (hZF : M.Models ZF)
local notation "I" => kp_pair_l (ZF.modelsKP hZF)

/-- 只要求实际字母载体可数；不把整个模型可数作为枚举的前提。 -/
theorem td_enum_l {Ω X R U A z : M.Domain}
    (carrier : ∀ x, M.mem x A ↔ M.mem x X ∧ Rd_entry_d x U R)
    (count : M.CardinalLessOrEqual I A Ω) (hz : M.mem z X) (letter : Rd_entry_d z U R) :
    ∃ E, Td_enum_d Ω X R U E := by
  obtain ⟨E,fn,onto⟩ := countable_surjection_zf_l hZF count ⟨z,(carrier z).mpr ⟨hz,letter⟩⟩
  exact ⟨E,(fn0_of_function_l (ZF.modelsKP hZF) fn).mono_target_l
    (fun x hx => ((carrier x).mp hx).1),
    fun _ x hx => ((carrier x).mp (fn.output_mem_of_pairMember hx)).2,
    fun x hx hU => onto x ((carrier x).mpr ⟨hx,hU⟩)⟩

/-- 重置使奇祖先列为空；已有合法字母直接满足零深度调度。 -/
theorem td_depth_zero_l (J : kpair_convention_l.Interpretation M)
    {Ω X R U z : M.Domain} (hΩ : M.IsOmega Ω) :
    ∃ d F, (∀ x, ¬ M.mem x d) ∧ Td_depth_d J Ω X R U d F ∧ Td_pick_d J Ω d F z := by
  obtain ⟨d,empty,hd⟩ := hΩ.1.1
  have product : M.IsCartesianProduct J d d Ω := fun p =>
    ⟨fun hp => (empty p hp).elim,fun ⟨i,hi,_⟩ => (empty i hi).elim⟩
  have fn : Fn0_d d X d := ⟨fun p hp => (empty p hp).elim,
    fun i hi => (empty i hi).elim,fun i hi => (empty i hi).elim⟩
  refine ⟨d,d,empty,⟨hd,⟨d,product,fn⟩,?_⟩,?_⟩
  · rintro p x ⟨q,_,hq⟩
    exact (empty q hq).elim
  · intro n _ _ _ succ
    exact (empty n succ.predecessor_mem).elim

/-- 从实际父表和父枚举构造新表。只用函数图及字母成员关系保持。 -/
theorem Td_depth_d.step_l {Ω X R Y S U V d F E j : M.Domain}
    (old : Td_depth_d I Ω X R U d F) (hΩ : M.IsOmega Ω)
    (edge : M.IsSetFunctionFromTo I j X Y)
    (image : ∀ x y, Rd_entry_d x y j → Rd_entry_d x U R → Rd_entry_d y V S)
    (enum : Fn0_d Ω X E)
    (letters : ∀ e x, Rd_entry_d e x E → Rd_entry_d x U R) :
    ∃ d' F', M.SuccessorOf d' d ∧ Td_depth_d I Ω Y S V d' F' ∧
      ∀ p y, Rd_entry_d p y F' ↔ Td_depth_next_d Ω d F E j p y := by
  obtain ⟨D,product,fn⟩ := old.table
  obtain ⟨d',succ,hd'⟩ := hΩ.1.2 d old.natural
  obtain ⟨D',product'⟩ := ZF.exists_cartesianProduct hZF I d' Ω
  let φ : BinarySchema 5 := {
    body := td_depth_next_m (.bound 2) (.bound 3) (.bound 4) (.bound 5) (.bound 6) (.bound 1) .newest }
  let ρ : Env M 5 := ⟨fun i => [Ω,d,F,E,j].get i,fun _ => d⟩
  have sat p y : φ.denote ρ p y ↔ Td_depth_next_d Ω d F E j p y :=
    td_depth_next_sat_l hZF.1 ..
  have total p (hp : M.mem p D') : ∃ y, φ.denote ρ p y := by
    obtain ⟨i,hi,e,he,pair⟩ := (product' p).mp hp
    have entry : ∃ x, M.mem x X ∧
        ((M.mem i d ∧ Rd_entry_d p x F) ∨ (i = d ∧ Rd_entry_d e x E)) := by
      rcases (succ i).mp hi with hi | eq
      · obtain ⟨x,hx,px⟩ := fn.2.1 p ((product p).mpr ⟨i,hi,e,he,pair⟩)
        exact ⟨x,hx,Or.inl ⟨hi,px⟩⟩
      · obtain ⟨x,hx,ex⟩ := enum.2.1 e he
        exact ⟨x,hx,Or.inr ⟨hZF.1.eq_of_same_members i d eq,ex⟩⟩
    obtain ⟨x,hx,value⟩ := entry
    obtain ⟨y,_,xy⟩ := edge.2.2 x hx
    exact ⟨y,(sat p y).mpr ⟨i,e,x,pair,he,value,xy⟩⟩
  have unique p (_ : M.mem p D') y y' (hy : φ.denote ρ p y) (hy' : φ.denote ρ p y') : y = y' := by
    obtain ⟨i,e,x,pair,_,value,xy⟩ := (sat p y).mp hy
    obtain ⟨i',e',x',pair',_,value',xy'⟩ := (sat p y').mp hy'
    obtain ⟨rfl,rfl⟩ := kpair_injective_l M pair' pair
    have eq : x = x' := by
      rcases value with ⟨hi,px⟩ | ⟨rfl,ex⟩ <;> rcases value' with ⟨hi',px'⟩ | ⟨eq,ex'⟩
      · exact (fn0_function_l (ZF.modelsKP hZF) fn).1.2 p x x' px px'
      · exact (KP.mem_irrefl_d (ZF.modelsKP hZF) d (eq ▸ hi)).elim
      · exact (KP.mem_irrefl_d (ZF.modelsKP hZF) _ hi').elim
      · exact (fn0_function_l (ZF.modelsKP hZF) enum).1.2 _ x x' ex ex'
    exact edge.1.2 x y y' xy (eq.symm ▸ xy')
  have target p y (_ : M.mem p D') (hy : φ.denote ρ p y) : M.mem y Y := by
    obtain ⟨_,_,_,_,_,_,xy⟩ := (sat p y).mp hy
    exact edge.output_mem_of_pairMember xy
  obtain ⟨F',fn',graph⟩ := ZF.exists_setFunctionFromTo_of_denote hZF I φ ρ total unique target
  have law p y : Rd_entry_d p y F' ↔ Td_depth_next_d Ω d F E j p y := by
    change M.PairMember I p y F' ↔ _
    rw [graph,sat]
    refine ⟨And.right,fun h => ⟨?_,h⟩⟩
    obtain ⟨i,e,x,pair,he,value,_⟩ := h
    have hi : M.mem i d' := (succ i).mpr (value.elim
      (fun h => Or.inl h.1) (fun h => Or.inr (h.1 ▸ fun _ => Iff.rfl)))
    exact (product' p).mpr ⟨i,hi,e,he,pair⟩
  refine ⟨d',F',succ,⟨hd',⟨D',product',fn0_of_function_l (ZF.modelsKP hZF) fn'⟩,?_⟩,law⟩
  intro p y py
  obtain ⟨i,e,x,_,_,value,xy⟩ := (law p y).mp py
  exact image x y xy
    (value.elim (fun h => old.letters p x h.2) (fun h => letters e x h.2))

/-- 从当前深度直接选字母。规范配对可能留有空号，空号使用已有合法字母。 -/
theorem Td_depth_d.pick_l {Ω X R U d F z₀ : M.Domain}
    (table : Td_depth_d I Ω X R U d F) (hΩ : M.IsOmega Ω)
    (hz : M.mem z₀ X) (letter : Rd_entry_d z₀ U R) :
    ∃ z, M.mem z X ∧ Rd_entry_d z U R ∧ Td_pick_d I Ω d F z := by
  classical
  by_cases task : ∃ n i e, M.SuccessorOf d n ∧ M.mem i Ω ∧ M.mem e Ω ∧ Oc_pair_d I i e n
  · obtain ⟨n,i,e,succ,hi,he,code⟩ := task
    have bound := oc_pair_left_bound_l I hZF hΩ hi he code
    have hid := ordinal_down_l (ZF.modelsKP hZF)
      (hΩ.members_areOrdinals (ZF.modelsKP hZF) i hi)
      (hΩ.members_areOrdinals (ZF.modelsKP hZF) d table.natural) bound succ.predecessor_mem
    obtain ⟨D,product,fn⟩ := table.table
    obtain ⟨p,pair⟩ := (I).total i e
    obtain ⟨z,hz,pz⟩ := fn.2.1 p ((product p).mpr ⟨i,hid,e,he,pair⟩)
    refine ⟨z,hz,table.letters p z pz,?_⟩
    intro n' i' e' p' succ' _ _ code' pair'
    have en : n' = n := by
      have on' := hΩ.members_areOrdinals (ZF.modelsKP hZF) n'
        (hΩ.transitive (ZF.modelsKP hZF) d table.natural n' succ'.predecessor_mem)
      exact succ'.predecessor_eq hZF.1 on' succ
    obtain ⟨ei,ee⟩ := oc_pair_injective_l I hZF (en ▸ code') code
    subst i' e'
    exact (I).unique pair pair' ▸ pz
  · exact ⟨z₀,hz,letter,fun n i e _ hs hi he code _ => (task ⟨n,i,e,hs,hi,he,code⟩).elim⟩

/-- 每个实际任务在其配对代码的下一深度命中；不含全局阶段命中前提。 -/
theorem Td_pick_d.hit_l {Ω d F z i e n p y : M.Domain}
    (pick : Td_pick_d I Ω d F z) (fn : M.IsSetFunction I F)
    (hi : M.mem i Ω) (he : M.mem e Ω) (code : Oc_pair_d I i e n)
    (succ : M.SuccessorOf d n) (pair : KPair_d M p i e) (value : Rd_entry_d p y F) :
    z = y :=
  fn.2 p z y
    (pick n i e p succ hi he code pair) value

end YesMetaZFC.SetTheory.LargeCardinal
