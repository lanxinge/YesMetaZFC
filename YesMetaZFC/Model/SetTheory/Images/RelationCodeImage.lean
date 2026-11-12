import YesMetaZFC.SetTheory.Ord.OrderType
import YesMetaZFC.SetTheory.InnerModel.Recursion.Graph
import YesMetaZFC.Model.Forcing.Ground.Collapse
import YesMetaZFC.SetTheory.Descriptive.Coding.RelationCode
import YesMetaZFC.Model.SetTheory.Images.BinaryImage

/-! # 成员满嵌入反射良序并保持实际坍塌值域

目标的良序最小元对源中每个实际子集仍适用。坍塌图的递归方程与
完整值域由成员满性逐成员保持；不要求两模型有相同幂集或全初等性。
-/
namespace YesMetaZFC.SetTheory
open Definitional.Project InnerModel Model.Forcing.Internal
universe u v
variable {M : Structure.{u}} {N : Structure.{v}} (hM : M.Models KP) (hN : N.Models KP)
  (e : M.Domain → N.Domain) (inj : Function.Injective e)
  (full : ∀ a y, N.mem y (e a) ↔ ∃ x, M.mem x a ∧ e x = y)
local notation "I" => kp_pair_l hM
local notation "J" => kp_pair_l hN
include full

theorem relation_image_l {R : M.Domain} (rel : M.IsSetRelation I R) : N.IsSetRelation J (e R) := by
  intro p hp
  obtain ⟨q,hq,rfl⟩ := (full R p).mp hp
  obtain ⟨a,b,pair⟩ := rel q hq
  exact ⟨e a,e b,image_kpair_l e full pair⟩

include inj

theorem wellorder_reflect_l {R D : M.Domain} (rel : M.IsSetRelation I R)
    (order : N.IsSetCodedWellOrder J (e R) (e D)) : M.IsSetCodedWellOrder I R D := by
  have mem {a b} := @image_member_l M N e inj full a b
  have edge := image_entry_iff_l e inj full (KP.exists_pair hM) hN.1
  have same {a b} (h : N.SameMembers (e a) (e b)) : M.SameMembers a b :=
    inj (hN.1.eq_of_same_members _ _ h) ▸ (fun _ => Iff.rfl)
  refine ⟨⟨rel,⟨?_,?_⟩,?_⟩,?_⟩
  · intro a ha aa
    exact order.linear.2.1.1 (e a) (mem.mpr ha) ((edge a a R).mp aa)
  · intro a ha b hb c hc ab bc
    exact (edge a c R).mpr (order.linear.2.1.2 (e a) (mem.mpr ha) (e b) (mem.mpr hb)
      (e c) (mem.mpr hc) ((edge a b R).mp ab) ((edge b c R).mp bc))
  · intro a ha b hb
    rcases order.linear.2.2 (e a) (mem.mpr ha) (e b) (mem.mpr hb) with eq | ab | ba
    · exact Or.inl (same eq)
    · exact Or.inr (Or.inl ((edge a b R).mpr ab))
    · exact Or.inr (Or.inr ((edge b a R).mpr ba))
  · intro S sub ⟨a,ha⟩
    obtain ⟨b,hb,least⟩ := order.least (e S) (fun y hy => by
      obtain ⟨x,hx,rfl⟩ := (full S y).mp hy
      exact mem.mpr (sub x hx)) ⟨e a,mem.mpr ha⟩
    obtain ⟨b₀,hb₀,rfl⟩ := (full S b).mp hb
    exact ⟨b₀,hb₀,fun x hx => (least (e x) (mem.mpr hx)).elim
      (fun eq => Or.inl (same eq)) (fun bx => Or.inr ((edge b₀ x R).mpr bx))⟩

/-- 实际良序坍塌图及其整个序型随成员满嵌入保持。 -/
theorem wellorder_type_image_l {R D α : M.Domain} (type : M.IsWellOrderType I R D α) :
    N.IsWellOrderType J (e R) (e D) (e α) := by
  obtain ⟨F,collapse,range⟩ := type
  have mem {a b} := @image_member_l M N e inj full a b
  have edge := image_entry_iff_l e inj full (KP.exists_pair hM) hN.1
  have function : M.IsSetFunctionFromTo I F D α := ⟨collapse.1,collapse.2.1,fun a ha => by
    obtain ⟨b,ab⟩ := (collapse.2.1 a).mp ha
    exact ⟨b,(range b).mpr ⟨a,ab⟩,ab⟩⟩
  have image : N.IsSetFunctionFromTo J (e F) (e D) (e α) := image_function_l e inj full function
  refine ⟨e F,⟨image.1,image.2.1,Structure.IsRelationInitialSegment.refl J (e R) (e D),?_⟩,?_⟩
  · intro a ha b ab y
    obtain ⟨a₀,b₀,old,rfl,rfl⟩ := (image_entries_l e full collapse.1.1 a b).mp ab
    have ha₀ := function.input_mem_of_pairMember old
    constructor
    · intro hy
      obtain ⟨y₀,hy₀,rfl⟩ := (full b₀ y).mp hy
      obtain ⟨p,hp,pa,py⟩ := (collapse.2.2.2 a₀ ha₀ b₀ old y₀).mp hy₀
      exact ⟨e p,mem.mpr hp,(edge p a₀ R).mp pa,(edge p y₀ F).mp py⟩
    · rintro ⟨p,hp,pa,py⟩
      obtain ⟨p₀,hp₀,rfl⟩ := (full D p).mp hp
      obtain ⟨p₁,y₀,py₀,ep,rfl⟩ := (image_entries_l e full collapse.1.1 (e p₀) y).mp py
      have eq : p₁ = p₀ := inj ep
      subst p₁
      exact mem.mpr ((collapse.2.2.2 a₀ ha₀ b₀ old y₀).mpr ⟨p₀,hp₀,(edge p₀ a₀ R).mpr pa,py₀⟩)
  · intro y
    constructor
    · intro hy
      obtain ⟨b,hb,rfl⟩ := (full α y).mp hy
      obtain ⟨a,ab⟩ := (range b).mp hb
      exact ⟨e a,(edge a b F).mp ab⟩
    · rintro ⟨a,ay⟩
      obtain ⟨a₀,b,ab,rfl,rfl⟩ := (image_entries_l e full collapse.1.1 a y).mp ay
      exact mem.mpr ((range b).mpr ⟨a₀,ab⟩)

end YesMetaZFC.SetTheory

/-! ## 同一良序实数的解码与原序型回收

规范自然数方块把全部关系读取降为 Δ₀。源中实际解码后，成员满嵌入
送出的载体和边与背景解码唯一相等。背景良序性反射，源的规范坍塌
值域再映回背景，由序型唯一性识别为指定原序数。
-/
namespace YesMetaZFC.SetTheory
open Definitional.Project InnerModel Descriptive Model.Forcing.Internal
universe u v
variable {M : Structure.{u}} {N : Structure.{v}} (hM : M.Models ZF) (hN : N.Models ZF)
  (e : M.Domain → N.Domain) (inj : Function.Injective e)
  (full : ∀ a y, N.mem y (e a) ↔ ∃ x, M.mem x a ∧ e x = y)
local notation "I" => kp_pair_l (ZF.modelsKP hM)
local notation "J" => kp_pair_l (ZF.modelsKP hN)
include inj full

theorem bc_edges_image_l {ω b R : M.Domain} (hw : M.IsOrdinal ω)
    (rel : M.IsSetRelation I R) (read : Bc_edges_d I ω b R) : Bc_edges_d J (e ω) (e b) (e R) := by
  obtain ⟨X,product⟩ := ZF.exists_cartesianProduct hM I ω ω
  obtain ⟨η,F,square⟩ := oc_square_exists_l hM hw product
  have square' := (oc_square_image_l e inj full (ZF.modelsKP hM) (ZF.modelsKP hN)).mp square
  have entry a d : Bc_entry_d ω X F b a d ↔ Bc_entry_d (e ω) (e X) (e F) (e b) (e a) (e d) := by
    let ρ : Env M 6 := ⟨fun i => [ω,X,F,b,a,d].get i,fun _ => ω⟩
    exact (bc_entry_sat_l hM.1 ρ (.bound 0) (.bound 1) (.bound 2) (.bound 3) (.bound 4) (.bound 5)).symm.trans
      ((delta0_image_l e inj full (bc_entry_delta_l ..) ρ).trans (bc_entry_sat_l hN.1 _ _ _ _ _ _ _))
  intro a d
  constructor
  · intro ad
    obtain ⟨a₀,d₀,old,rfl,rfl⟩ := (image_entries_l e full rel a d).mp ad
    exact (bc_entry_pair_l hN square').mp ((entry a₀ d₀).mp ((bc_entry_pair_l hM square).mpr ((read a₀ d₀).mp old)))
  · intro code
    obtain ⟨a₀,_,rfl⟩ := (full ω a).mp code.1
    obtain ⟨d₀,_,rfl⟩ := (full ω d).mp code.2.1
    have old := (read a₀ d₀).mpr ((bc_entry_pair_l hM square).mp ((entry a₀ d₀).mpr ((bc_entry_pair_l hN square').mpr code)))
    exact (image_entry_iff_l e inj full (KP.exists_pair (ZF.modelsKP hM)) hN.1 a₀ d₀ R).mp old

theorem Descriptive.Wo_read_d.image_l {ω b D R : M.Domain} (hw : M.IsOrdinal ω)
    (read : Wo_read_d I ω b D R) : Wo_read_d J (e ω) (e b) (e D) (e R) := by
  obtain ⟨U,rel,edges,diag,rr,graph⟩ := read
  have mem {a b} := @image_member_l M N e inj full a b
  have edge := image_entry_iff_l e inj full (KP.exists_pair (ZF.modelsKP hM)) hN.1
  refine ⟨e U,⟨relation_image_l (ZF.modelsKP hM) (ZF.modelsKP hN) e full rel.1,?_⟩,
    bc_edges_image_l hM hN e inj full hw rel.1 edges,?_,
    relation_image_l (ZF.modelsKP hM) (ZF.modelsKP hN) e full rr,?_⟩
  · intro a b ab
    obtain ⟨a₀,b₀,old,rfl,rfl⟩ := (image_entries_l e full rel.1 a b).mp ab
    exact ⟨mem.mpr (rel.2 a₀ b₀ old).1,mem.mpr (rel.2 a₀ b₀ old).2⟩
  · intro a
    constructor
    · intro ha
      obtain ⟨a₀,ha₀,rfl⟩ := (full D a).mp ha
      exact (edge a₀ a₀ U).mp ((diag a₀).mp ha₀)
    · intro aa
      obtain ⟨a₀,b₀,old,ea,eb⟩ := (image_entries_l e full rel.1 a a).mp aa
      have eq : b₀ = a₀ := inj (eb.trans ea.symm)
      subst b₀
      exact ea ▸ mem.mpr ((diag a₀).mpr old)
  · intro a b
    constructor
    · intro ab
      obtain ⟨a₀,b₀,old,rfl,rfl⟩ := (image_entries_l e full rr a b).mp ab
      obtain ⟨ha,hb,ne,ab⟩ := (graph a₀ b₀).mp old
      exact ⟨mem.mpr ha,mem.mpr hb,fun eq => ne (inj eq),(edge a₀ b₀ U).mp ab⟩
    · rintro ⟨ha,hb,ne,ab⟩
      obtain ⟨a₀,ha₀,rfl⟩ := (full D a).mp ha
      obtain ⟨b₀,hb₀,rfl⟩ := (full D b).mp hb
      exact (edge a₀ b₀ R).mp ((graph a₀ b₀).mpr
        ⟨ha₀,hb₀,fun eq => ne (congrArg e eq),(edge a₀ b₀ U).mpr ab⟩)

/-- 编码实数已经在源中时，背景给定的良序序型也有同一个源序数原像。 -/
theorem Descriptive.Wo_code_d.pull_type_l {ω b : M.Domain} {β : N.Domain} (hw : M.IsOmega ω)
    (code : Wo_code_d J (e ω) (e b) β) : ∃ α, M.IsOrdinal α ∧ e α = β ∧ Wo_code_d I ω b α := by
  obtain ⟨binary,D',R',read',order',type'⟩ := code
  obtain ⟨D,R,read⟩ := wo_decode_l hM hw b
  have moved := read.image_l hM hN e inj full (hw.isOrdinal (ZF.modelsKP hM))
  obtain ⟨eD,eR⟩ := moved.unique_l hN read'
  subst D' R'
  have rel : M.IsSetRelation I R := read.elim fun _ h => h.2.2.2.1
  have order := wellorder_reflect_l (ZF.modelsKP hM) (ZF.modelsKP hN) e inj full rel order'
  obtain ⟨α,type,_⟩ := ZF.wellOrderType_existsUnique hM I order
  have typeM := wellorder_type_image_l (ZF.modelsKP hM) (ZF.modelsKP hN) e inj full type
  obtain ⟨γ,_,unique⟩ := ZF.wellOrderType_existsUnique hN J order'
  exact ⟨α,Structure.IsWellOrderType.isOrdinal hM I order type,
    (unique (e α) typeM).trans (unique β type').symm,
    (bc_binary_image_l e inj full hM.1 hN.1).mpr binary,D,R,read,order,type⟩

end YesMetaZFC.SetTheory
