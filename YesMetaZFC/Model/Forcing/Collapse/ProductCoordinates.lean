import YesMetaZFC.Model.Forcing.Collapse.NameCode
import YesMetaZFC.Model.Forcing.Order.GenericTreeGround
import YesMetaZFC.SetTheory.CumulativeClosure
import YesMetaZFC.Model.Forcing.Order.GlobalDense

/-! # 坍缩条件的逐位置值交换

在两条给定条件共有的位置交换其值，其他字母和位置保持不变。
位置始终不动，因而作用保留初段定义域；全部关系均有模型内公式。
-/
namespace YesMetaZFC.Model.Forcing.Internal
open SetTheory SetTheory.Definitional.Project
universe u
variable {M : Structure.{u}}

def Swap_val_d {α : Type u} (a b x y : α) : Prop :=
  (x = a ∧ y = b) ∨ (x = b ∧ y = a) ∨ (x ≠ a ∧ x ≠ b ∧ y = x)

def swap_val_m {n} (a b x y : Term n) : Formula 1 n := set[n] ⟪
  (⌜x⌝ₛ = ⌜a⌝ₛ ∧ ⌜y⌝ₛ = ⌜b⌝ₛ) ∨ (⌜x⌝ₛ = ⌜b⌝ₛ ∧ ⌜y⌝ₛ = ⌜a⌝ₛ) ∨
    (¬ ⌜x⌝ₛ = ⌜a⌝ₛ ∧ ¬ ⌜x⌝ₛ = ⌜b⌝ₛ ∧ ⌜y⌝ₛ = ⌜x⌝ₛ)⟫
derive_free_closed swap_val_m

def Fs_val_d (p q i x y : M.Domain) : Prop :=
  (∃ a b, Entry_d M i a p ∧ Entry_d M i b q ∧ Swap_val_d a b x y) ∨
    (¬ (∃ a b, Entry_d M i a p ∧ Entry_d M i b q)) ∧ y = x

def fs_val_m {n} (p q i x y : Term n) : Formula 1 n := set[n] ⟪
  (∃ a b, ⌜entry_m⌝ₚ(⌜i⌝ₛ,a,⌜p⌝ₛ) ∧ ⌜entry_m⌝ₚ(⌜i⌝ₛ,b,⌜q⌝ₛ) ∧
    ⌜swap_val_m⌝ₚ(a,b,⌜x⌝ₛ,⌜y⌝ₛ)) ∨
    (¬ (∃ a b, ⌜entry_m⌝ₚ(⌜i⌝ₛ,a,⌜p⌝ₛ) ∧ ⌜entry_m⌝ₚ(⌜i⌝ₛ,b,⌜q⌝ₛ))) ∧ ⌜y⌝ₛ = ⌜x⌝ₛ⟫
derive_free_closed fs_val_m

def Fs_swap_d (p q s t : M.Domain) : Prop :=
  (∀ v, M.mem v t → ∃ i y, KPair_d M v i y) ∧
    ∀ i y, Entry_d M i y t ↔ ∃ x, Entry_d M i x s ∧ Fs_val_d p q i x y

def fs_swap_m {n} (p q s t : Term n) : Formula 1 n := set[n] ⟪
  ⌜Formula.isRelation kpair_convention_l⌝ₚ(⌜t⌝ₛ) ∧
    (∀ i y, ⌜entry_m⌝ₚ(i,y,⌜t⌝ₛ) ↔ ∃ x, ⌜entry_m⌝ₚ(i,x,⌜s⌝ₛ) ∧
      ⌜fs_val_m⌝ₚ(⌜p⌝ₛ,⌜q⌝ₛ,i,x,y))⟫
derive_free_closed fs_swap_m

theorem swap_val_sat_l (hE : Extensional M) {n} (ρ : Env M n) (a b x y : Term n) :
    Formula.satisfies ρ (swap_val_m a b x y) ↔
      Swap_val_d (a.eval ρ) (b.eval ρ) (x.eval ρ) (y.eval ρ) := by
  simp only [swap_val_m,Swap_val_d,Formula.satisfies_disj_iff,Formula.satisfies_conj_iff,
    Formula.satisfies_neg_iff,Formula.satisfies_extensionalEq_iff_eq hE]

theorem fs_val_sat_l (hE : Extensional M) {n} (ρ : Env M n) (p q i x y : Term n) :
    Formula.satisfies ρ (fs_val_m p q i x y) ↔
      Fs_val_d (p.eval ρ) (q.eval ρ) (i.eval ρ) (x.eval ρ) (y.eval ρ) := by
  simp only [fs_val_m,Fs_val_d,Formula.satisfies_disj_iff,Formula.satisfies_conj_iff,
    Formula.satisfies_exists_iff,Formula.satisfies_neg_iff,entry_sat_l M hE,swap_val_sat_l hE,
    Formula.satisfies_extensionalEq_iff_eq hE,Definitional.Term.eval_weaken,Definitional.Term.eval_newest]

theorem fs_swap_sat_l (hE : Extensional M) {n} (ρ : Env M n) (p q s t : Term n) :
    Formula.satisfies ρ (fs_swap_m p q s t) ↔
      Fs_swap_d (p.eval ρ) (q.eval ρ) (s.eval ρ) (t.eval ρ) := by
  simp only [fs_swap_m,Fs_swap_d,Formula.isRelation,kpair_convention_l,
    Formula.satisfies_conj_iff,Formula.satisfies_forallMem_iff,Formula.satisfies_exists_iff,
    Formula.satisfies_forall_iff,Formula.satisfies_iff_iff,kpair_sat_l M hE,entry_sat_l M hE,
    fs_val_sat_l hE,Definitional.Term.eval_weaken,Definitional.Term.eval_newest]
  rfl

theorem Swap_val_d.symm_l {α : Type u} {a b x y : α} (h : Swap_val_d a b x y) : Swap_val_d a b y x := by
  rcases h with ⟨rfl,rfl⟩ | ⟨rfl,rfl⟩ | ⟨ha,hb,rfl⟩
  · exact Or.inr (Or.inl ⟨rfl,rfl⟩)
  · exact Or.inl ⟨rfl,rfl⟩
  · exact Or.inr (Or.inr ⟨ha,hb,rfl⟩)

theorem Swap_val_d.unique_l {α : Type u} {a b x y z : α}
    (h : Swap_val_d a b x y) (k : Swap_val_d a b x z) : y = z := by
  rcases h with ⟨hx,hy⟩ | ⟨hx,hy⟩ | ⟨ha,hb,hy⟩ <;>
    rcases k with ⟨kx,kz⟩ | ⟨kx,kz⟩ | ⟨ka,kb,kz⟩ <;> simp_all

theorem Fs_val_d.symm_l {p q i x y : M.Domain} (h : Fs_val_d p q i x y) : Fs_val_d p q i y x := by
  rcases h with ⟨a,b,ia,ib,h⟩ | ⟨h,rfl⟩
  · exact Or.inl ⟨a,b,ia,ib,h.symm_l⟩
  · exact Or.inr ⟨h,rfl⟩

theorem Fs_val_d.unique_l {p q i x y z : M.Domain}
    (hp : ∀ i a b, Entry_d M i a p → Entry_d M i b p → a = b)
    (hq : ∀ i a b, Entry_d M i a q → Entry_d M i b q → a = b)
    (h : Fs_val_d p q i x y) (k : Fs_val_d p q i x z) : y = z := by
  rcases h with ⟨a,b,ia,ib,h⟩ | ⟨h,hy⟩
  · rcases k with ⟨c,d,ic,id,k⟩ | ⟨k,_⟩
    · have ea := hp i a c ia ic
      have eb := hq i b d ib id
      subst c d
      exact h.unique_l k
    · exact (k ⟨a,b,ia,ib⟩).elim
  · rcases k with ⟨a,b,ia,ib,_⟩ | ⟨_,kz⟩
    · exact (h ⟨a,b,ia,ib⟩).elim
    · exact hy.trans kz.symm

end YesMetaZFC.Model.Forcing.Internal

/-! ## 有限支撑坍缩乘积的实际坐标块

条件以长度 n 的有限坐标块呈示，每个坐标仍是原字母表上的初段函数。
末尾允许空条件；长度因而可增加而不改变原坐标。这是保留填充的有限支撑呈示。
-/
namespace YesMetaZFC.Model.Forcing.Internal
open SetTheory SetTheory.Definitional.Project
universe u
variable {M : Structure.{u}} {𝒞 : OrderedPairConvention} (I : 𝒞.Interpretation M)

structure Fp_at_d (ω A n p : M.Domain) : Prop where
  function : M.IsSetFunction I p
  domain : M.IsDomainOf I n p
  coordinates : ∀ i s, M.PairMember I i s p →
    ∃ κ m, M.PairMember I i κ A ∧ M.mem m ω ∧ M.IsSetFunctionFromTo I s m κ

def fp_at_m {d} (ω A n p : Term d) : Formula 1 d := set[d] ⟪
  ⌜Formula.isFunction 𝒞⌝ₚ(⌜p⌝ₛ) ∧ ⌜Formula.isDomain 𝒞⌝ₚ(⌜n⌝ₛ,⌜p⌝ₛ) ∧
    (∀ i s, ⌜Formula.orderedPairMem 𝒞⌝ₚ(i,s,⌜p⌝ₛ) →
      ∃ κ m, ⌜Formula.orderedPairMem 𝒞⌝ₚ(i,κ,⌜A⌝ₛ) ∧ m ∈ ⌜ω⌝ₛ ∧
        ⌜Formula.isFunctionFromTo 𝒞⌝ₚ(s,m,κ))⟫
derive_free_closed fp_at_m

def Fp_le_d (p q : M.Domain) : Prop :=
  ∀ i s, M.PairMember I i s q → ∃ t, M.PairMember I i t p ∧ M.MemberSubset s t

def fp_le_m {d} (p q : Term d) : Formula 1 d := set[d] ⟪
  ∀ i s, ⌜Formula.orderedPairMem 𝒞⌝ₚ(i,s,⌜q⌝ₛ) →
    ∃ t, ⌜Formula.orderedPairMem 𝒞⌝ₚ(i,t,⌜p⌝ₛ) ∧ s ⊆ t⟫
derive_free_closed fp_le_m

theorem fp_at_sat_l (hE : Extensional M) {d} (ρ : Env M d) (ω A n p : Term d) :
    Formula.satisfies ρ (fp_at_m (𝒞 := 𝒞) ω A n p) ↔
      Fp_at_d I (ω.eval ρ) (A.eval ρ) (n.eval ρ) (p.eval ρ) := by
  simp only [fp_at_m,Formula.satisfies_conj_iff,Formula.satisfies_isFunction_iff I hE,
    Formula.satisfies_isDomain_iff I,Formula.satisfies_forall_iff,Formula.satisfies_imp_iff,
    Formula.satisfies_orderedPairMem_iff I,Formula.satisfies_exists_iff,Formula.satisfies_mem_iff,
    Formula.satisfies_isFunctionFromTo_iff I hE,Definitional.Term.eval_weaken]
  exact ⟨fun ⟨f,dom,c⟩ => ⟨f,dom,c⟩,fun h => ⟨h.function,h.domain,h.coordinates⟩⟩

theorem fp_le_sat_l {d} (ρ : Env M d) (p q : Term d) :
    Formula.satisfies ρ (fp_le_m (𝒞 := 𝒞) p q) ↔ Fp_le_d I (p.eval ρ) (q.eval ρ) := by
  simp only [fp_le_m,Fp_le_d,Formula.satisfies_forall_iff,Formula.satisfies_imp_iff,
    Formula.satisfies_orderedPairMem_iff I,Formula.satisfies_exists_iff,Formula.satisfies_conj_iff,
    Formula.satisfies_subset_iff,Definitional.Term.eval_weaken]
  rfl

theorem Fp_le_d.refl_l (p : M.Domain) : Fp_le_d I p p := fun _ s h => ⟨s,h,fun _ hx => hx⟩

theorem Fp_le_d.trans_l {p q r : M.Domain} (h : Fp_le_d I p q) (k : Fp_le_d I q r) : Fp_le_d I p r := by
  intro i s is
  obtain ⟨t,it,st⟩ := k i s is
  obtain ⟨u,iu,tu⟩ := h i t it
  exact ⟨u,iu,fun x hx => tu x (st x hx)⟩

theorem Fp_le_d.domain_l {ω A n m p q : M.Domain} (h : Fp_le_d I p q)
    (hp : Fp_at_d I ω A n p) (hq : Fp_at_d I ω A m q) : M.MemberSubset m n := by
  intro i hi
  obtain ⟨s,is⟩ := (hq.domain i).mp hi
  obtain ⟨t,it,_⟩ := h i s is
  exact (hp.domain i).mpr ⟨t,it⟩

end YesMetaZFC.Model.Forcing.Internal

/-! ## 可变字母表上的实际有限支撑坍缩乘积

全部条件从有限序列包络中分离，关系逐坐标加强。
固定有限长度给出前缀偏序；全乘积条件的限制仍是同一原坐标块。
-/
namespace YesMetaZFC.Model.Forcing.Internal
open SetTheory SetTheory.Definitional.Project
universe u
variable {M : Structure.{u}} (hZF : M.Models ZF)
local notation "I" => kpair_interpretation_l M (And.left hZF) (KP.exists_pair (ZF.modelsKP hZF))

structure Fp_product_d (ω A P R : M.Domain) : Prop where
  conditions : ∀ p, M.mem p P ↔ ∃ n, M.mem n ω ∧ Fp_at_d I ω A n p
  order : ∀ p q, Entry_d M p q R ↔ M.mem p P ∧ M.mem q P ∧ Fp_le_d I p q

/-- 固定长度前缀有自己的条件域和关系图，排除值为该条件域自身。 -/
structure Fp_prefix_d (ω A n C S : M.Domain) : Prop where
  conditions : ∀ p, M.mem p C ↔ Fp_at_d I ω A n p
  order : ∀ p q, Entry_d M p q S ↔ M.mem p C ∧ M.mem q C ∧ Fp_le_d I p q

theorem Fp_prefix_d.order_l {ω A n C S : M.Domain} (h : Fp_prefix_d hZF ω A n C S) : Cond_order_d M C S C :=
  ⟨fun p hp => (h.order p p).mpr ⟨hp,hp,Fp_le_d.refl_l I p⟩,
    fun p q r hp _ hr pq qr => (h.order p r).mpr
      ⟨hp,hr,((h.order p q).mp pq).2.2.trans_l I ((h.order q r).mp qr).2.2⟩,
    fun p _ pC => (KP.mem_irrefl_d (ZF.modelsKP hZF) C ((h.order p C).mp pC).2.1).elim⟩

theorem Fp_product_d.order_l {ω A P R : M.Domain} (h : Fp_product_d hZF ω A P R) : Cond_order_d M P R P :=
  ⟨fun p hp => (h.order p p).mpr ⟨hp,hp,Fp_le_d.refl_l I p⟩,
    fun p q r hp _ hr pq qr => (h.order p r).mpr
      ⟨hp,hr,((h.order p q).mp pq).2.2.trans_l I ((h.order q r).mp qr).2.2⟩,
    fun p _ pP => (KP.mem_irrefl_d (ZF.modelsKP hZF) P ((h.order p P).mp pP).2.1).elim⟩

/-- 任意实际字母表列都产生整个有限支撑乘积，而非仅给出条件规格。 -/
theorem fp_product_l {ω A U : M.Domain} (hw : M.IsOmega ω) (fa : M.IsSetFunctionFromTo I A ω U) :
    ∃ P R, Fp_product_d hZF ω A P R := by
  obtain ⟨Z,union⟩ := KP.exists_union (ZF.modelsKP hZF) U
  obtain ⟨S,rows⟩ := ZF.fseq_space_exists_l I hZF hw Z
  obtain ⟨W,blocks⟩ := ZF.fseq_space_exists_l I hZF hw S
  have bounded {n p} (h : Fp_at_d I ω A n p) : M.IsSetFunctionFromTo I p n S := by
    refine ⟨h.function,h.domain,?_⟩
    intro i hi
    obtain ⟨s,is⟩ := (h.domain i).mp hi
    obtain ⟨κ,m,ia,hm,fs⟩ := h.coordinates i s is
    have fs' : M.IsSetFunctionFromTo I s m Z := ⟨fs.1,fs.2.1,fun j hj => by
      obtain ⟨x,hx,jx⟩ := fs.2.2 j hj
      exact ⟨x,(union x).mpr ⟨κ,fa.output_mem_of_pairMember ia,hx⟩,jx⟩⟩
    exact ⟨s,(rows s).mpr ⟨m,hm,fs'⟩,is⟩
  let ρ : Env M 2 := ⟨fun i => [ω,A].get i,fun _ => A⟩
  let φ : UnarySchema 2 := { body := .existsE (.conj (.mem .newest (.bound 2))
    (fp_at_m (𝒞 := kpair_convention_l) (.bound 2) (.bound 3) .newest (.bound 1))) }
  have sat p : φ.denote ρ p ↔ ∃ n, M.mem n ω ∧ Fp_at_d I ω A n p := by
    simp only [φ,UnarySchema.denote,Formula.satisfies_exists_iff,Formula.satisfies_conj_iff,
      Formula.satisfies_mem_iff,fp_at_sat_l I hZF.1]
    rfl
  obtain ⟨P,members⟩ := ZF.separation_exists_d hZF φ ρ W
  have space p : M.mem p P ↔ ∃ n, M.mem n ω ∧ Fp_at_d I ω A n p :=
    (members p).trans ⟨fun h => (sat p).mp h.2,
      fun ⟨n,hn,h⟩ => ⟨(blocks p).mpr ⟨n,hn,bounded h⟩,(sat p).mpr ⟨n,hn,h⟩⟩⟩
  let η : Env M 0 := ⟨Fin.elim0,fun _ => A⟩
  let ψ : BinarySchema 0 := { body := fp_le_m (𝒞 := kpair_convention_l) (.bound 1) .newest }
  obtain ⟨R,_,relation⟩ := ZF.exists_setRelationOn_of_denote hZF I ψ η P
  exact ⟨P,R,space,fun p q => (relation p q).trans
    (and_congr_right fun _ => and_congr_right fun _ => fp_le_sat_l I ..)⟩

theorem Fp_at_d.restrict_l {ω A n k p : M.Domain} (h : Fp_at_d I ω A n p)
    (sub : M.MemberSubset k n) : ∃ q, M.IsRestrictionOf I q p k ∧ Fp_at_d I ω A k q := by
  obtain ⟨q,cut⟩ := ZF.exists_restriction hZF I p k
  have fn : M.IsSetFunction I q := ⟨cut.1,fun i s t is it =>
    h.function.2 i s t ((cut.2 i s).mp is).2 ((cut.2 i t).mp it).2⟩
  refine ⟨q,cut,fn,fun i => ⟨?_,?_⟩,fun i s is => h.coordinates i s ((cut.2 i s).mp is).2⟩
  · intro hi
    obtain ⟨s,is⟩ := (h.domain i).mp (sub i hi)
    exact ⟨s,(cut.2 i s).mpr ⟨hi,is⟩⟩
  · rintro ⟨s,is⟩
    exact ((cut.2 i s).mp is).1

/-- 固定前缀及其逐坐标关系都是原模型中的实际集合。 -/
theorem Fp_product_d.prefix_l {ω A P R n : M.Domain} (h : Fp_product_d hZF ω A P R)
    (hn : M.mem n ω) : ∃ C S, Fp_prefix_d hZF ω A n C S := by
  let ρ : Env M 3 := ⟨fun i => [ω,A,n].get i,fun _ => n⟩
  let φ : UnarySchema 3 := { body := fp_at_m (𝒞 := kpair_convention_l) (.bound 1) (.bound 2) (.bound 3) .newest }
  obtain ⟨C,members⟩ := ZF.separation_exists_d hZF φ ρ P
  have space q : M.mem q C ↔ Fp_at_d I ω A n q :=
    (members q).trans ⟨fun h => (fp_at_sat_l I hZF.1 ..).mp h.2,
      fun hq => ⟨(h.conditions q).mpr ⟨n,hn,hq⟩,(fp_at_sat_l I hZF.1 ..).mpr hq⟩⟩
  let η : Env M 0 := ⟨Fin.elim0,fun _ => n⟩
  let ψ : BinarySchema 0 := { body := fp_le_m (𝒞 := kpair_convention_l) (.bound 1) .newest }
  obtain ⟨S,_,relation⟩ := ZF.exists_setRelationOn_of_denote hZF I ψ η C
  exact ⟨C,S,space,fun p q => (relation p q).trans
    (and_congr_right fun _ => and_congr_right fun _ => fp_le_sat_l I ..)⟩

end YesMetaZFC.Model.Forcing.Internal

/-! ## 全乘积条件域的统一秩界

所有行都落在同一个有限列空间，所有有限支撑块再落在第二重有限列空间。
只需原字母集的共同包络和极限秩层，不需要不可达性或全乘积名字前提。
-/
namespace YesMetaZFC.Model.Forcing.Internal
open SetTheory SetTheory.Definitional.Project SetTheory.InnerModel
universe u
variable {M : Structure.{u}} (hZF : M.Models ZF)
local notation "I" => kp_pair_l (ZF.modelsKP hZF)

theorem Fp_product_d.rank_mem_l {ω A P R δ V B : M.Domain}
    (product : Fp_product_d hZF ω A P R) (hw : M.IsOmega ω)
    (rank : V_d I δ V) (limit : M.IsLimitOrdinal δ) (hω : M.mem ω V) (hB : M.mem B V)
    (bound : ∀ i κ, Entry_d M i κ A → M.MemberSubset κ B) : M.mem P V := by
  obtain ⟨S,rows⟩ := ZF.fseq_space_exists_l I hZF hw B
  have hS := ZF.v_fseq_mem_l I hZF rank limit hw hω hB rows
  obtain ⟨W,blocks⟩ := ZF.fseq_space_exists_l I hZF hw S
  apply v_subset_mem_l I rank (ZF.v_fseq_mem_l I hZF rank limit hw hω hS blocks)
  intro p hp
  obtain ⟨n,hn,block⟩ := (product.conditions p).mp hp
  refine (blocks p).mpr ⟨n,hn,block.function,block.domain,fun i hi => ?_⟩
  obtain ⟨s,is⟩ := (block.domain i).mp hi
  obtain ⟨κ,m,ia,hm,row⟩ := block.coordinates i s is
  refine ⟨s,(rows s).mpr ⟨m,hm,row.1,row.2.1,fun j hj => ?_⟩,is⟩
  obtain ⟨a,ha,ja⟩ := row.2.2 j hj
  exact ⟨a,bound i κ ia a ha,ja⟩

end YesMetaZFC.Model.Forcing.Internal

/-! ## 有限乘积前缀的末坐标分解

追加和分解都产生实际集合图。逐坐标加强恰好分解为旧前缀加强和末坐标加强，
为下一前缀与二元积的实际序同构提供完整数学内容。
-/
namespace YesMetaZFC.Model.Forcing.Internal
open SetTheory SetTheory.Definitional.Project
universe u
variable {M : Structure.{u}} (hZF : M.Models ZF)
local notation "I" => kpair_interpretation_l M (And.left hZF) (KP.exists_pair (ZF.modelsKP hZF))

theorem Fp_at_d.snoc_l {ω A n m q κ s : M.Domain} (hw : M.IsOmega ω)
    (hn : M.mem n ω) (succ : M.SuccessorOf m n) (fq : Fp_at_d I ω A n q)
    (alphabet : Entry_d M n κ A)
    (fs : ∃ k, M.mem k ω ∧ M.IsSetFunctionFromTo I s k κ) :
    ∃ t, Fp_at_d I ω A m t ∧ Fseq_end_d I ω t q s := by
  obtain ⟨V,range⟩ := ZF.exists_range_of_setFunction hZF I fq.function fq.domain
  obtain ⟨W,insert⟩ := KP.exists_insert (ZF.modelsKP hZF) V s
  have fn : M.IsSetFunctionFromTo I q n W := ⟨fq.function,fq.domain,fun i hi => by
    obtain ⟨p,ip⟩ := (fq.domain i).mp hi
    exact ⟨p,(insert p).mpr (Or.inl ((range p).mpr ⟨i,ip⟩)),ip⟩⟩
  obtain ⟨m',t,hm',ft,ending⟩ := ZF.fseq_end_exists_l I hZF hw hn fn ((insert s).mpr (Or.inr rfl))
  have saved := ending
  obtain ⟨a,b,last⟩ := saved
  have en := last.prefix_sequence.2.2.2.eq hZF.1 fq.domain
  have em := last.source.2.2.2.eq hZF.1 ft.2.1
  subst b a
  have em := last.length_successor.eq hZF.1 succ
  subst m'
  refine ⟨t,⟨ft.1,ft.2.1,?_⟩,ending⟩
  intro i p ip
  rcases (ending.entries_l I hZF.1 fq.domain i p).mp ip with ip | ⟨rfl,rfl⟩
  · exact fq.coordinates i p ip
  · obtain ⟨k,hk,fs⟩ := fs
    exact ⟨κ,k,alphabet,hk,fs⟩

theorem Fp_at_d.split_l {ω A n m t κ B : M.Domain} (hw : M.IsOmega ω)
    (hn : M.mem n ω) (hm : M.mem m ω) (succ : M.SuccessorOf m n)
    (fa : M.IsSetFunction I A) (alphabet : Entry_d M n κ A)
    (space : Fseq_space_d I ω κ B) (ft : Fp_at_d I ω A m t) :
    ∃ q s, Fp_at_d I ω A n q ∧ M.mem s B ∧ Fseq_end_d I ω t q s := by
  obtain ⟨q,cut,fq⟩ := ft.restrict_l hZF (fun i hi => (succ i).mpr (Or.inl hi))
  obtain ⟨s,ns⟩ := (ft.domain n).mp succ.predecessor_mem
  obtain ⟨κ',k,entry,hk,fs⟩ := ft.coordinates n s ns
  have eq := fa.2 n κ' κ entry alphabet
  subst κ'
  have no := hw.members_areOrdinals (ZF.modelsKP hZF) n hn
  have mo := hw.members_areOrdinals (ZF.modelsKP hZF) m hm
  exact ⟨q,s,fq,(space s).mpr ⟨k,hk,fs⟩,m,n,
    ⟨⟨hm,mo,ft.function,ft.domain⟩,hn,succ,⟨hn,no,fq.function,fq.domain⟩,cut,ns⟩⟩

/-- 末项分解上的顺序恰为两个坐标的积顺序。 -/
theorem fp_snoc_order_l {ω n t q s t' q' s' : M.Domain}
    (domain : M.IsDomainOf I n q) (domain' : M.IsDomainOf I n q')
    (end₀ : Fseq_end_d I ω t q s) (end₁ : Fseq_end_d I ω t' q' s') :
    Fp_le_d I t t' ↔ Fp_le_d I q q' ∧ M.MemberSubset s' s := by
  have entries := end₀.entries_l I hZF.1 domain
  have entries' := end₁.entries_l I hZF.1 domain'
  have no : ¬ M.mem n n := KP.mem_irrefl_d (ZF.modelsKP hZF) n
  constructor
  · intro le
    refine ⟨?_,?_⟩
    · intro i a ia
      obtain ⟨b,ib,ab⟩ := le i a ((entries' i a).mpr (Or.inl ia))
      rcases (entries i b).mp ib with ib | ⟨eq,_⟩
      · exact ⟨b,ib,ab⟩
      · exact (no (eq ▸ (domain' i).mpr ⟨a,ia⟩)).elim
    · obtain ⟨b,nb,sb⟩ := le n s' ((entries' n s').mpr (Or.inr ⟨rfl,rfl⟩))
      rcases (entries n b).mp nb with nb | ⟨_,eq⟩
      · exact (no ((domain n).mpr ⟨b,nb⟩)).elim
      · exact eq ▸ sb
  · rintro ⟨le,sub⟩ i a ia
    rcases (entries' i a).mp ia with ia | ⟨ei,ea⟩
    · obtain ⟨b,ib,ab⟩ := le i a ia
      exact ⟨b,(entries i b).mpr (Or.inl ib),ab⟩
    · subst i a
      exact ⟨s,(entries n s).mpr (Or.inr ⟨rfl,rfl⟩),sub⟩

/-- 任意有限前缀都有实际最大条件：每个已列出的坐标取空序列。 -/
theorem Fp_prefix_d.top_l {ω A n C S U : M.Domain} (stage : Fp_prefix_d hZF ω A n C S)
    (hw : M.IsOmega ω) (hn : M.mem n ω) (fa : M.IsSetFunctionFromTo I A ω U) :
    ∃ b, M.mem b C ∧ ∀ p, M.mem p C → Entry_d M p b S := by
  obtain ⟨o,empty,ho⟩ := hw.1.1
  obtain ⟨O,pair⟩ := KP.exists_pair (ZF.modelsKP hZF) o o
  obtain ⟨b,fb,entries⟩ := ZF.exists_constantFunction hZF I (source := n) ((pair o).mpr (Or.inl rfl))
  have typed : Fp_at_d I ω A n b := by
    refine ⟨fb.1,fb.2.1,?_⟩
    intro i s is
    obtain ⟨hi,eq⟩ := (entries i s).mp is
    subst s
    obtain ⟨κ,_,iκ⟩ := fa.2.2 i (hw.transitive (ZF.modelsKP hZF) n hn i hi)
    have seq := Structure.IsSequenceOfLength.empty I empty
    exact ⟨κ,o,iκ,ho,seq.2.1,seq.2.2,fun i hi => (empty i hi).elim⟩
  have hb := (stage.conditions b).mpr typed
  refine ⟨b,hb,fun p hp => (stage.order p b).mpr ⟨hp,hb,?_⟩⟩
  intro i s is
  obtain ⟨hi,rfl⟩ := (entries i s).mp is
  obtain ⟨t,it⟩ := ((stage.conditions p).mp hp).domain i |>.mp hi
  exact ⟨t,it,fun x hx => (empty x hx).elim⟩

end YesMetaZFC.Model.Forcing.Internal

/-! ## 有限坐标块的任意前缀替换与补长

按实际函数图替换前 n 个坐标，其余坐标保持原值。构造覆盖全部内部有限长度，
供有限前缀泛型的投影、名字比较和派生实数并集共同使用。
-/
namespace YesMetaZFC.Model.Forcing.Internal
open SetTheory SetTheory.Definitional.Project
universe u
variable {M : Structure.{u}} (hZF : M.Models ZF)
local notation "I" => kpair_interpretation_l M (And.left hZF) (KP.exists_pair (ZF.modelsKP hZF))

theorem Fp_at_d.splice_l {ω A n m p q : M.Domain} (fp : Fp_at_d I ω A m p)
    (fq : Fp_at_d I ω A n q) (sub : M.MemberSubset n m) :
    ∃ r, Fp_at_d I ω A m r ∧ M.IsRestrictionOf I q r n ∧ Fp_le_d I r q ∧
      ∀ i s, Entry_d M i s r ↔ Entry_d M i s q ∨ (¬ M.mem i n ∧ Entry_d M i s p) := by
  let ρ : Env M 3 := ⟨fun k => [n,p,q].get k,fun _ => p⟩
  let φ : BinarySchema 3 := { body := set[5] ⟪
    (⌜(.bound 1 : Term 5)⌝ₛ ∈ ⌜(.bound 2 : Term 5)⌝ₛ ∧
      ⌜entry_m⌝ₚ(⌜(.bound 1 : Term 5)⌝ₛ,⌜(.bound 0 : Term 5)⌝ₛ,⌜(.bound 4 : Term 5)⌝ₛ)) ∨
    (⌜(.bound 1 : Term 5)⌝ₛ ∉ ⌜(.bound 2 : Term 5)⌝ₛ ∧
      ⌜entry_m⌝ₚ(⌜(.bound 1 : Term 5)⌝ₛ,⌜(.bound 0 : Term 5)⌝ₛ,⌜(.bound 3 : Term 5)⌝ₛ))⟫ }
  have read i s : φ.denote ρ i s ↔ (M.mem i n ∧ Entry_d M i s q) ∨ (¬ M.mem i n ∧ Entry_d M i s p) := by
    simp only [φ,BinarySchema.denote,Formula.satisfies_disj_iff,Formula.satisfies_conj_iff,
      Formula.satisfies_neg_iff,Formula.satisfies_mem_iff,entry_sat_l M hZF.1]
    rfl
  have total i (hi : M.mem i m) : ∃ s, φ.denote ρ i s := by
    rcases Classical.em (M.mem i n) with hin | hin
    · obtain ⟨s,is⟩ := (fq.domain i).mp hin
      exact ⟨s,(read i s).mpr (Or.inl ⟨hin,is⟩)⟩
    · obtain ⟨s,is⟩ := (fp.domain i).mp hi
      exact ⟨s,(read i s).mpr (Or.inr ⟨hin,is⟩)⟩
  have unique i s t (hs : φ.denote ρ i s) (ht : φ.denote ρ i t) : s = t := by
    rcases (read i s).mp hs with ⟨hin,is⟩ | ⟨hin,is⟩ <;>
      rcases (read i t).mp ht with ⟨hin',it⟩ | ⟨hin',it⟩
    · exact fq.function.2 i s t is it
    · exact (hin' hin).elim
    · exact (hin hin').elim
    · exact fp.function.2 i s t is it
  obtain ⟨V,range⟩ := ZF.exists_functionalImage hZF φ ρ m total unique
  obtain ⟨r,fn,graph⟩ := ZF.exists_setFunctionFromTo_of_denote hZF I φ ρ total
    (fun i _ => unique i) (fun i s hi hs => (range s).mpr ⟨i,hi,hs⟩)
  have entries i s : Entry_d M i s r ↔ Entry_d M i s q ∨ (¬ M.mem i n ∧ Entry_d M i s p) := by
    apply (graph i s).trans
    rw [read]
    exact ⟨fun h => h.2.elim (fun h => Or.inl h.2) Or.inr,fun h => h.elim
      (fun h => ⟨sub i ((fq.domain i).mpr ⟨s,h⟩),Or.inl ⟨(fq.domain i).mpr ⟨s,h⟩,h⟩⟩)
      (fun h => ⟨(fp.domain i).mpr ⟨s,h.2⟩,Or.inr h⟩)⟩
  refine ⟨r,⟨fn.1,fn.2.1,fun i s is => ((entries i s).mp is).elim
    (fq.coordinates i s) (fun h => fp.coordinates i s h.2)⟩,⟨fq.function.1,?_⟩,?_,entries⟩
  · intro i s
    exact ⟨fun is => ⟨(fq.domain i).mpr ⟨s,is⟩,(entries i s).mpr (Or.inl is)⟩,
      fun ⟨hin,is⟩ => ((entries i s).mp is).elim id (fun h => (h.1 hin).elim)⟩
  · exact fun i s is => ⟨s,(entries i s).mpr (Or.inl is),fun _ h => h⟩

theorem fp_splice_lower_l {n p s q r : M.Domain}
    (cut : M.IsRestrictionOf I s p n) (le : Fp_le_d I q s)
    (entries : ∀ i a, Entry_d M i a r ↔ Entry_d M i a q ∨ (¬ M.mem i n ∧ Entry_d M i a p)) :
    Fp_le_d I r p := by
  intro i a ia
  rcases Classical.em (M.mem i n) with hin | hin
  · obtain ⟨b,ib,sub⟩ := le i a ((cut.2 i a).mpr ⟨hin,ia⟩)
    exact ⟨b,(entries i b).mpr (Or.inl ib),sub⟩
  · exact ⟨a,(entries i a).mpr (Or.inr ⟨hin,ia⟩),fun _ h => h⟩

theorem Fp_at_d.pad_l {ω A n m q W : M.Domain} (hw : M.IsOmega ω) (hm : M.mem m ω)
    (fa : M.IsSetFunctionFromTo I A ω W) (fq : Fp_at_d I ω A n q) (sub : M.MemberSubset n m) :
    ∃ r, Fp_at_d I ω A m r ∧ M.IsRestrictionOf I q r n ∧ Fp_le_d I r q := by
  obtain ⟨P,U,product⟩ := fp_product_l hZF hw fa
  obtain ⟨C,S,stage⟩ := product.prefix_l hZF hm
  obtain ⟨p,hp,_⟩ := stage.top_l hZF hw hm fa
  obtain ⟨r,fr,cut,le,_⟩ := ((stage.conditions p).mp hp).splice_l hZF fq sub
  exact ⟨r,fr,cut,le⟩

end YesMetaZFC.Model.Forcing.Internal

/-! ## 全乘积和有限前缀的同一泛型投影

投影滤子由原泛型条件在短前缀上的加强关系定义。任意前缀替换给出稠密要求的提升，
因此投影命中原模型全部稠密集；全乘积和长有限前缀分别提供真实实例。
-/
namespace YesMetaZFC.Model.Forcing.Internal
open SetTheory SetTheory.Definitional.Project
universe u
variable {M : Structure.{u}} {𝒞 : OrderedPairConvention} (I : 𝒞.Interpretation M)

def Fp_project_d (C : M.Domain) (G : M.Domain → Prop) (q : M.Domain) : Prop :=
  M.mem q C ∧ ∃ p, G p ∧ Fp_le_d I p q

variable (hZF : M.Models ZF)
local notation "J" => kpair_interpretation_l M (And.left hZF) (KP.exists_pair (ZF.modelsKP hZF))

private theorem fp_project_generic_l {ω A n C S D V : M.Domain} {G : M.Domain → Prop}
    (small : Fp_prefix_d hZF ω A n C S)
    (typed : ∀ p, M.mem p D → ∃ m, Fp_at_d J ω A m p)
    (saturated : ∀ m p q, Fp_at_d J ω A m p → Fp_at_d J ω A m q → M.mem q D → M.mem p D)
    (order : ∀ p q, Entry_d M p q V ↔ M.mem p D ∧ M.mem q D ∧ Fp_le_d J p q)
    (long : ∀ p, M.mem p D → ∃ r q, M.mem r D ∧ Fp_le_d J r p ∧ M.mem q C ∧ Fp_le_d J r q)
    (generic : Generic_d M D V D G) : Generic_d M C S C (Fp_project_d J C G) := by
  have positive {p B : M.Domain} (hp : M.mem p B) : p ≠ B := fun eq => KP.mem_irrefl_d (ZF.modelsKP hZF) B (eq ▸ hp)
  have cutle {p r q : M.Domain} (fq : Fp_at_d J ω A n q) (cut : M.IsRestrictionOf J r p n)
      (le : Fp_le_d J p q) : Fp_le_d J r q := by
    intro i a ia
    obtain ⟨b,ib,ab⟩ := le i a ia
    exact ⟨b,(cut.2 i b).mpr ⟨(fq.domain i).mpr ⟨a,ia⟩,ib⟩,ab⟩
  have liftD (B : M.Domain) : ∃ E, ∀ p, M.mem p E ↔ M.mem p D ∧ ∃ q, M.mem q B ∧ M.mem q C ∧ Fp_le_d J p q := by
    let ρ : Env M 2 := ⟨fun k => [B,C].get k,fun _ => B⟩
    let φ : UnarySchema 2 := { body := .existsE (.conj (.mem .newest (.bound 2))
      (.conj (.mem .newest (.bound 3)) (fp_le_m (𝒞 := kpair_convention_l) (.bound 1) .newest))) }
    obtain ⟨E,sep⟩ := ZF.separation_exists_d hZF φ ρ D
    refine ⟨E,fun p => (sep p).trans (and_congr_right fun _ => ?_)⟩
    simp only [φ,Formula.satisfies_exists_iff,Formula.satisfies_conj_iff,Formula.satisfies_mem_iff,fp_le_sat_l J]
    rfl
  refine ⟨fun q hq => ⟨hq.1,positive hq.1⟩,?_,?_,?_,?_⟩
  · obtain ⟨p,hp⟩ := generic.inhabited
    obtain ⟨E,members⟩ := liftD C
    obtain ⟨r,hr,hE⟩ := generic.meets p hp E (by
      intro s hs
      obtain ⟨r,q,hr,rs,hq,rq⟩ := long s hs.1
      exact ⟨r,⟨hr,positive hr,(order r s).mpr ⟨hr,hs.1,rs⟩⟩,(members r).mpr ⟨hr,q,hq,hq,rq⟩⟩)
    obtain ⟨_,q,hq,_,rq⟩ := (members r).mp hE
    exact ⟨q,hq,r,hr,rq⟩
  · rintro p q ⟨_,r,hr,rp⟩ hq pq
    exact ⟨hq,r,hr,rp.trans_l J ((small.order p q).mp pq).2.2⟩
  · rintro p q ⟨hp,a,ha,ap⟩ ⟨hq,b,hb,bq⟩
    obtain ⟨r,hr,ra,rb⟩ := generic.directed a b ha hb
    obtain ⟨m,fr⟩ := typed r (generic.proper r hr).1
    have rp := ((order r a).mp ra).2.2.trans_l J ap
    have rq := ((order r b).mp rb).2.2.trans_l J bq
    have fp := (small.conditions p).mp hp
    obtain ⟨s,cut,fs⟩ := fr.restrict_l hZF (rp.domain_l J fr fp)
    have hs := (small.conditions s).mpr fs
    have rs : Fp_le_d J r s := fun i a ia => ⟨a,((cut.2 i a).mp ia).2,fun _ h => h⟩
    exact ⟨s,⟨hs,r,hr,rs⟩,(small.order s p).mpr ⟨hs,hp,cutle fp cut rp⟩,
      (small.order s q).mpr ⟨hs,hq,cutle ((small.conditions q).mp hq) cut rq⟩⟩
  · rintro q ⟨hq,p,hp,pq⟩ B dense
    obtain ⟨E,members⟩ := liftD B
    obtain ⟨r,hr,rE⟩ := generic.meets p hp E (by
      intro s hs
      obtain ⟨m,fs⟩ := typed s hs.1
      have sq := ((order s p).mp hs.2.2).2.2.trans_l J pq
      have fq := (small.conditions q).mp hq
      have sub := sq.domain_l J fs fq
      obtain ⟨a,cut,fa⟩ := fs.restrict_l hZF sub
      have ha := (small.conditions a).mpr fa
      obtain ⟨b,ba,bB⟩ := dense a ⟨ha,positive ha,(small.order a q).mpr ⟨ha,hq,cutle fq cut sq⟩⟩
      have fb := (small.conditions b).mp ba.1
      obtain ⟨r,fr,_,rb,entries⟩ := fs.splice_l hZF fb sub
      have rs := fp_splice_lower_l hZF cut ((small.order b a).mp ba.2.2).2.2 entries
      have rD := saturated m r s fr fs hs.1
      exact ⟨r,⟨rD,positive rD,(order r s).mpr ⟨rD,hs.1,rs⟩⟩,(members r).mpr ⟨rD,b,bB,ba.1,rb⟩⟩)
    obtain ⟨_,b,bB,bC,rb⟩ := (members r).mp rE
    exact ⟨b,⟨bC,r,hr,rb⟩,bB⟩

theorem Fp_prefix_d.project_generic_l {ω A n m C S D V : M.Domain} {G : M.Domain → Prop}
    (small : Fp_prefix_d hZF ω A n C S) (large : Fp_prefix_d hZF ω A m D V)
    (sub : M.MemberSubset n m) (generic : Generic_d M D V D G) : Generic_d M C S C (Fp_project_d J C G) := by
  apply fp_project_generic_l hZF small (fun p hp => ⟨m,(large.conditions p).mp hp⟩) ?_ large.order ?_ generic
  · intro k p q fp fq hq
    have eq := fq.domain.eq hZF.1 ((large.conditions q).mp hq).domain
    exact (large.conditions p).mpr (eq ▸ fp)
  · intro p hp
    obtain ⟨q,cut,fq⟩ := ((large.conditions p).mp hp).restrict_l hZF sub
    exact ⟨p,q,hp,Fp_le_d.refl_l J p,(small.conditions q).mpr fq,fun i a ia =>
      ⟨a,((cut.2 i a).mp ia).2,fun _ h => h⟩⟩

theorem Fp_product_d.project_generic_l {ω A n C S P V W : M.Domain} {G : M.Domain → Prop}
    (hw : M.IsOmega ω) (hn : M.mem n ω) (fa : M.IsSetFunctionFromTo J A ω W)
    (product : Fp_product_d hZF ω A P V) (small : Fp_prefix_d hZF ω A n C S)
    (generic : Generic_d M P V P G) : Generic_d M C S C (Fp_project_d J C G) := by
  apply fp_project_generic_l hZF small (fun p hp => ((product.conditions p).mp hp).elim fun m h => ⟨m,h.2⟩) ?_ product.order ?_ generic
  · intro m p q fp fq hq
    obtain ⟨k,hk,fq'⟩ := (product.conditions q).mp hq
    have eq := fq.domain.eq hZF.1 fq'.domain
    exact (product.conditions p).mpr ⟨m,eq.symm ▸ hk,fp⟩
  · intro p hp
    obtain ⟨m,hm,fp⟩ := (product.conditions p).mp hp
    rcases (hw.isOrdinal (ZF.modelsKP hZF)).wellOrder.linear.compare n hn m hm with eq | lt | gt
    · obtain ⟨q,cut,fq⟩ := fp.restrict_l hZF (fun i hi => (eq i).mp hi)
      exact ⟨p,q,hp,Fp_le_d.refl_l J p,(small.conditions q).mpr fq,fun i a ia => ⟨a,((cut.2 i a).mp ia).2,fun _ h => h⟩⟩
    · obtain ⟨q,cut,fq⟩ := fp.restrict_l hZF ((hw.members_areOrdinals (ZF.modelsKP hZF) m hm).transitive n lt)
      exact ⟨p,q,hp,Fp_le_d.refl_l J p,(small.conditions q).mpr fq,fun i a ia => ⟨a,((cut.2 i a).mp ia).2,fun _ h => h⟩⟩
    · obtain ⟨r,fr,_,rp⟩ := fp.pad_l hZF hw hn fa ((hw.members_areOrdinals (ZF.modelsKP hZF) n hn).transitive m gt)
      exact ⟨r,r,(product.conditions r).mpr ⟨n,hn,fr⟩,rp,(small.conditions r).mpr fr,Fp_le_d.refl_l J r⟩

/-- 固定长度前缀由全乘积及其定义域唯一决定，不另依赖字母表呈示。 -/
theorem Fp_prefix_d.product_read_l {ω A n C S P V : M.Domain}
    (stage : Fp_prefix_d hZF ω A n C S) (product : Fp_product_d hZF ω A P V) (hn : M.mem n ω) :
    (∀ p, M.mem p C ↔ M.mem p P ∧ M.IsDomainOf J n p) ∧
      ∀ p q, Entry_d M p q S ↔ M.mem p C ∧ M.mem q C ∧ Entry_d M p q V := by
  have read p : M.mem p C ↔ M.mem p P ∧ M.IsDomainOf J n p := by
    constructor
    · intro hp
      have fp := (stage.conditions p).mp hp
      exact ⟨(product.conditions p).mpr ⟨n,hn,fp⟩,fp.domain⟩
    · rintro ⟨hp,dom⟩
      obtain ⟨m,_,fp⟩ := (product.conditions p).mp hp
      have eq := fp.domain.eq hZF.1 dom
      exact (stage.conditions p).mpr (eq ▸ fp)
  exact ⟨read,fun p q => (stage.order p q).trans (and_congr_right fun hp => and_congr_right fun hq =>
    ⟨fun le => (product.order p q).mpr ⟨((read p).mp hp).1,((read q).mp hq).1,le⟩,
      fun pq => ((product.order p q).mp pq).2.2⟩)⟩

/-- 两个字母表呈示同一全乘积时，固定长度的前缀也相同。 -/
theorem Fp_prefix_d.rebase_l {ω A A' n C S P V : M.Domain}
    (stage : Fp_prefix_d hZF ω A n C S) (product : Fp_product_d hZF ω A P V)
    (other : Fp_product_d hZF ω A' P V) (hn : M.mem n ω) : Fp_prefix_d hZF ω A' n C S := by
  refine ⟨fun p => ((stage.product_read_l hZF product hn).1 p).trans ?_,stage.order⟩
  constructor
  · rintro ⟨hp,dom⟩
    obtain ⟨m,_,fp⟩ := (other.conditions p).mp hp
    exact fp.domain.eq hZF.1 dom ▸ fp
  · intro fp
    exact ⟨(other.conditions p).mpr ⟨n,hn,fp⟩,fp.domain⟩

end YesMetaZFC.Model.Forcing.Internal

/-! ## 逐位置一致的乘积条件有实际共同加强

每行是内部有限初段函数，公共位置一致即意味着两行按包含可比。
在较长外层定义域上逐行取较大者；替代给出同一模型中的共同加强。
-/
namespace YesMetaZFC.Model.Forcing.Internal
open SetTheory SetTheory.Definitional.Project
universe u
variable {M : Structure.{u}} (hZF : M.Models ZF)
local notation "I" => kpair_interpretation_l M (And.left hZF) (KP.exists_pair (ZF.modelsKP hZF))

def Fp_agree_d (n p q : M.Domain) : Prop := ∀ i, M.mem i n → ∀ a b,
  Entry_d M i a p → Entry_d M i b q → Agree_d I a b

private theorem fs_comparable_l {ω X Y n m p q : M.Domain} (hw : M.IsOmega ω)
    (hn : M.mem n ω) (hm : M.mem m ω) (fp : M.IsSetFunctionFromTo I p n X)
    (fq : M.IsSetFunctionFromTo I q m Y) (agree : Agree_d I p q) :
    M.MemberSubset p q ∨ M.MemberSubset q p := by
  have sub {X Y n m p q} (fp : M.IsSetFunctionFromTo I p n X) (fq : M.IsSetFunctionFromTo I q m Y)
      (agree : Agree_d I p q) (nm : M.MemberSubset n m) : M.MemberSubset p q := by
    intro v hv
    obtain ⟨i,x,pair⟩ := fp.1.1 v hv
    obtain ⟨y,_,iy⟩ := fq.2.2 i (nm i (fp.input_mem_of_pairMember ⟨v,pair,hv⟩))
    obtain ⟨w,pair',hw⟩ := (agree i x y ⟨v,pair,hv⟩ iy).symm ▸ iy
    exact (I).unique pair' pair ▸ hw
  rcases (hw.isOrdinal (ZF.modelsKP hZF)).wellOrder.linear.compare n hn m hm with eq | lt | gt
  · exact Or.inl (sub fp fq agree (fun i hi => (eq i).mp hi))
  · exact Or.inl (sub fp fq agree ((hw.members_areOrdinals (ZF.modelsKP hZF) m hm).transitive n lt))
  · exact Or.inr (sub fq fp (fun i y x iy ix => (agree i x y ix iy).symm)
      ((hw.members_areOrdinals (ZF.modelsKP hZF) n hn).transitive m gt))

private theorem fp_join_l {ω A n m p q : M.Domain} (hw : M.IsOmega ω)
    (fp : Fp_at_d I ω A n p) (fq : Fp_at_d I ω A m q) (nm : M.MemberSubset n m)
    (agree : ∀ i a b, Entry_d M i a p → Entry_d M i b q → Agree_d I a b) :
    ∃ r, Fp_at_d I ω A m r ∧ Fp_le_d I r p ∧ Fp_le_d I r q := by
  let ρ : Env M 2 := ⟨fun k => [p,q].get k,fun _ => p⟩
  let φ : BinarySchema 2 := { body := set[4] ⟪
    (⌜entry_m⌝ₚ(⌜(.bound 1 : Term 4)⌝ₛ,⌜(.bound 0 : Term 4)⌝ₛ,⌜(.bound 2 : Term 4)⌝ₛ) ∨
      ⌜entry_m⌝ₚ(⌜(.bound 1 : Term 4)⌝ₛ,⌜(.bound 0 : Term 4)⌝ₛ,⌜(.bound 3 : Term 4)⌝ₛ)) ∧
    (∀ a, (⌜entry_m⌝ₚ(⌜(.bound 1 : Term 4)⌝ₛ,a,⌜(.bound 2 : Term 4)⌝ₛ) ∨
      ⌜entry_m⌝ₚ(⌜(.bound 1 : Term 4)⌝ₛ,a,⌜(.bound 3 : Term 4)⌝ₛ)) → a ⊆ ⌜(.bound 0 : Term 4)⌝ₛ)⟫ }
  have sat i a : φ.denote ρ i a ↔ (Entry_d M i a p ∨ Entry_d M i a q) ∧
      ∀ b, (Entry_d M i b p ∨ Entry_d M i b q) → M.MemberSubset b a := by
    simp only [φ,BinarySchema.denote,Formula.satisfies_conj_iff,Formula.satisfies_disj_iff,
      Formula.satisfies_forall_iff,Formula.satisfies_imp_iff,Formula.satisfies_subset_iff,entry_sat_l M hZF.1,Definitional.Term.eval_weaken]
    rfl
  have total i (hi : M.mem i m) : ∃ a, φ.denote ρ i a := by
    obtain ⟨b,ib⟩ := (fq.domain i).mp hi
    rcases Classical.em (∃ a, Entry_d M i a p) with ⟨a,ia⟩ | no
    · obtain ⟨X,k,iX,hk,fa⟩ := fp.coordinates i a ia
      obtain ⟨Y,l,iY,hl,fb⟩ := fq.coordinates i b ib
      rcases fs_comparable_l hZF hw hk hl fa fb (agree i a b ia ib) with ab | ba
      · exact ⟨b,(sat i b).mpr ⟨Or.inr ib,fun c hc => hc.elim
          (fun ic => fp.function.2 i c a ic ia ▸ ab) (fun ic => fq.function.2 i c b ic ib ▸ fun _ h => h)⟩⟩
      · exact ⟨a,(sat i a).mpr ⟨Or.inl ia,fun c hc => hc.elim
          (fun ic => fp.function.2 i c a ic ia ▸ fun _ h => h) (fun ic => fq.function.2 i c b ic ib ▸ ba)⟩⟩
    · exact ⟨b,(sat i b).mpr ⟨Or.inr ib,fun c hc => hc.elim
        (fun ic => (no ⟨c,ic⟩).elim) (fun ic => fq.function.2 i c b ic ib ▸ fun _ h => h)⟩⟩
  have unique i a b (ha : φ.denote ρ i a) (hb : φ.denote ρ i b) : a = b := by
    obtain ⟨ia,boundA⟩ := (sat i a).mp ha
    obtain ⟨ib,boundB⟩ := (sat i b).mp hb
    exact hZF.1.eq_of_same_members a b (fun v => ⟨boundB a ia v,boundA b ib v⟩)
  obtain ⟨W,range⟩ := ZF.exists_functionalImage hZF φ ρ m total unique
  obtain ⟨r,fn,entries⟩ := ZF.exists_setFunctionFromTo_of_denote hZF I φ ρ total
    (fun i _ => unique i) (fun i a hi ha => (range a).mpr ⟨i,hi,ha⟩)
  have below {s} (bounds : ∀ i a, Entry_d M i a s → M.mem i m)
      (old : ∀ i a, Entry_d M i a s → Entry_d M i a p ∨ Entry_d M i a q) : Fp_le_d I r s := by
    intro i a ia
    obtain ⟨b,_,ib⟩ := fn.2.2 i (bounds i a ia)
    exact ⟨b,ib,((sat i b).mp ((entries i b).mp ib).2).2 a (old i a ia)⟩
  exact ⟨r,⟨fn.1,fn.2.1,fun i a ia => (((sat i a).mp ((entries i a).mp ia).2).1).elim
    (fp.coordinates i a) (fq.coordinates i a)⟩,
    below (fun i a ia => nm i ((fp.domain i).mpr ⟨a,ia⟩)) (fun _ _ => Or.inl),
    below (fun i a ia => (fq.domain i).mpr ⟨a,ia⟩) (fun _ _ => Or.inr)⟩

theorem Fp_product_d.compatible_l {ω A P R p q : M.Domain} (hw : M.IsOmega ω)
    (product : Fp_product_d hZF ω A P R) (hp : M.mem p P) (hq : M.mem q P)
    (agree : ∀ i a b, Entry_d M i a p → Entry_d M i b q → Agree_d I a b) : Cmp_d M P R P p q := by
  obtain ⟨n,hn,fp⟩ := (product.conditions p).mp hp
  obtain ⟨m,hm,fq⟩ := (product.conditions q).mp hq
  have result {n m p q} (fp : Fp_at_d I ω A n p) (fq : Fp_at_d I ω A m q) (hm : M.mem m ω)
      (nm : M.MemberSubset n m) (agree : ∀ i a b, Entry_d M i a p → Entry_d M i b q → Agree_d I a b) :
      ∃ r, M.mem r P ∧ Fp_le_d I r p ∧ Fp_le_d I r q := by
    obtain ⟨r,fr,rp,rq⟩ := fp_join_l hZF hw fp fq nm agree
    exact ⟨r,(product.conditions r).mpr ⟨m,hm,fr⟩,rp,rq⟩
  have common : ∃ r, M.mem r P ∧ Fp_le_d I r p ∧ Fp_le_d I r q := by
    rcases (hw.isOrdinal (ZF.modelsKP hZF)).wellOrder.linear.compare n hn m hm with eq | lt | gt
    · exact result fp fq hm (fun i hi => (eq i).mp hi) agree
    · exact result fp fq hm ((hw.members_areOrdinals (ZF.modelsKP hZF) m hm).transitive n lt) agree
    · obtain ⟨r,hr,rq,rp⟩ := result fq fp hn ((hw.members_areOrdinals (ZF.modelsKP hZF) n hn).transitive m gt)
        (fun i b a ib ia k y x ky kx => (agree i a b ia ib k x y kx ky).symm)
      exact ⟨r,hr,rp,rq⟩
  obtain ⟨r,hr,rp,rq⟩ := common
  exact ⟨r,⟨hr,fun eq => KP.mem_irrefl_d (ZF.modelsKP hZF) P (eq ▸ hr),(product.order r p).mpr ⟨hr,hp,rp⟩⟩,
    (product.order r q).mpr ⟨hr,hq,rq⟩⟩

end YesMetaZFC.Model.Forcing.Internal

/-! ## 前缀与固定空前缀尾条件的实际拼接

拼接关系记录完整图方程。有限前缀域以及尾条件的共同前缀，使整块的加强
恰好分解为前缀加强和尾条件加强；内部有限长度仍可变。
-/
namespace YesMetaZFC.Model.Forcing.Internal
open SetTheory SetTheory.Definitional.Project
universe u
variable {M : Structure.{u}}

def Ft_join_d (n q t p : M.Domain) : Prop :=
  (∀ v, M.mem v p → ∃ i s, KPair_d M v i s) ∧
    ∀ i s, Entry_d M i s p ↔ Entry_d M i s q ∨ (¬ M.mem i n ∧ Entry_d M i s t)

def ft_join_m {d} (n q t p : Term d) : Formula 1 d := set[d] ⟪
  ⌜Formula.isRelation kpair_convention_l⌝ₚ(⌜p⌝ₛ) ∧
  (∀ i s, ⌜entry_m⌝ₚ(i,s,⌜p⌝ₛ) ↔ ⌜entry_m⌝ₚ(i,s,⌜q⌝ₛ) ∨
    (i ∉ ⌜n⌝ₛ ∧ ⌜entry_m⌝ₚ(i,s,⌜t⌝ₛ)))⟫
derive_free_closed ft_join_m

theorem ft_join_sat_l (hE : Extensional M) {d}
    (ρ : Env M d) (n q t p : Term d) :
    Formula.satisfies ρ (ft_join_m n q t p) ↔ Ft_join_d (n.eval ρ) (q.eval ρ) (t.eval ρ) (p.eval ρ) := by
  simp only [ft_join_m,Ft_join_d,Formula.isRelation,kpair_convention_l,Formula.satisfies_conj_iff,
    Formula.satisfies_forallMem_iff,Formula.satisfies_exists_iff,kpair_sat_l M hE,
    Formula.satisfies_forall_iff,Formula.satisfies_iff_iff,Formula.satisfies_disj_iff,
    Formula.satisfies_neg_iff,Formula.satisfies_mem_iff,entry_sat_l M hE,Definitional.Term.eval_weaken]
  rfl

theorem Ft_join_d.unique_l (hE : Extensional M) {n q t p p' : M.Domain}
    (h : Ft_join_d n q t p) (k : Ft_join_d n q t p') : p = p' :=
  entry_ext_l M hE h.1 k.1 (fun i s => (h.2 i s).trans (k.2 i s).symm)

variable (hZF : M.Models ZF)
local notation "I" => kpair_interpretation_l M (And.left hZF) (KP.exists_pair (ZF.modelsKP hZF))

theorem Ft_join_d.prefix_l {n q t p : M.Domain} (h : Ft_join_d n q t p)
    (rel : M.IsSetRelation I q) (domain : M.IsDomainOf I n q) : M.IsRestrictionOf I q p n := by
  refine ⟨rel,fun i s => ⟨fun is => ⟨(domain i).mpr ⟨s,is⟩,(h.2 i s).mpr (Or.inl is)⟩,?_⟩⟩
  rintro ⟨hi,is⟩
  exact ((h.2 i s).mp is).elim id (fun h => (h.1 hi).elim)

/-- 任意尾块和原前缀实际产生同一全乘积中的拼接块。 -/
theorem Fp_at_d.join_l {ω A n m b q t : M.Domain} (tail : Fp_at_d I ω A m t)
    (front : Fp_at_d I ω A n q) (base : M.IsDomainOf I n b) (cut : M.IsRestrictionOf I b t n) :
    ∃ p, Fp_at_d I ω A m p ∧ Ft_join_d n q t p := by
  have sub : M.MemberSubset n m := fun i hi => by
    obtain ⟨s,is⟩ := (base i).mp hi
    exact (tail.domain i).mpr ⟨s,((cut.2 i s).mp is).2⟩
  obtain ⟨p,fp,_,_,entries⟩ := tail.splice_l hZF front sub
  exact ⟨p,fp,fp.function.1,entries⟩

/-- 全条件的长度覆盖前缀时，取原限制并把尾部的前缀重置为指定基块。 -/
theorem Fp_at_d.tail_split_l {ω A n m b p : M.Domain} (fp : Fp_at_d I ω A m p)
    (base : Fp_at_d I ω A n b) (sub : M.MemberSubset n m) :
    ∃ q t, Fp_at_d I ω A n q ∧ M.IsRestrictionOf I q p n ∧ Fp_at_d I ω A m t ∧
      M.IsRestrictionOf I b t n ∧ Ft_join_d n q t p := by
  obtain ⟨q,cut,fq⟩ := fp.restrict_l hZF sub
  obtain ⟨t,ft,reset,_,entries⟩ := fp.splice_l hZF base sub
  refine ⟨q,t,fq,cut,ft,reset,fp.function.1,fun i s => ⟨?_,?_⟩⟩
  · intro is
    rcases Classical.em (M.mem i n) with hi | hi
    · exact Or.inl ((cut.2 i s).mpr ⟨hi,is⟩)
    · exact Or.inr ⟨hi,(entries i s).mpr (Or.inr ⟨hi,is⟩)⟩
  · rintro (is | ⟨hi,is⟩)
    · exact ((cut.2 i s).mp is).2
    · exact ((entries i s).mp is).elim (fun ib => (hi ((base.domain i).mpr ⟨s,ib⟩)).elim) And.right

theorem Ft_join_d.order_l {n b q q' t t' p p' : M.Domain}
    (h : Ft_join_d n q t p) (h' : Ft_join_d n q' t' p')
    (domain : M.IsDomainOf I n q) (domain' : M.IsDomainOf I n q')
    (cut : M.IsRestrictionOf I b t n) (cut' : M.IsRestrictionOf I b t' n) :
    Fp_le_d I p p' ↔ Fp_le_d I q q' ∧ Fp_le_d I t t' := by
  constructor
  · intro le
    constructor
    · intro i s is
      obtain ⟨r,ir,sr⟩ := le i s ((h'.2 i s).mpr (Or.inl is))
      exact ⟨r,((h.2 i r).mp ir).elim id (fun hn => (hn.1 ((domain' i).mpr ⟨s,is⟩)).elim),sr⟩
    · intro i s is
      rcases Classical.em (M.mem i n) with hi | hi
      · exact ⟨s,((cut.2 i s).mp ((cut'.2 i s).mpr ⟨hi,is⟩)).2,fun _ h => h⟩
      · obtain ⟨r,ir,sr⟩ := le i s ((h'.2 i s).mpr (Or.inr ⟨hi,is⟩))
        exact ⟨r,((h.2 i r).mp ir).elim (fun iq => (hi ((domain i).mpr ⟨r,iq⟩)).elim) And.right,sr⟩
  · rintro ⟨old,tail⟩ i s is
    rcases (h'.2 i s).mp is with is | ⟨hi,is⟩
    · obtain ⟨r,ir,sr⟩ := old i s is
      exact ⟨r,(h.2 i r).mpr (Or.inl ir),sr⟩
    · obtain ⟨r,ir,sr⟩ := tail i s is
      exact ⟨r,(h.2 i r).mpr (Or.inr ⟨hi,ir⟩),sr⟩

end YesMetaZFC.Model.Forcing.Internal

/-! ## 全乘积稠密任务与冻结前缀相容

把原全乘积稠密集投影到当前有限前缀；该投影是原模型中的实际稠密集合。
当前前缀泛型命中它，给出同一稠密集中的有限条件及已经接受的精确前缀。
先追加一个空坐标再使用稠密性，因此余下任务非空且有实际内部自然数终点。
-/
namespace YesMetaZFC.Model.Forcing.Internal
open SetTheory SetTheory.Definitional.Project
universe u
variable {M : Structure.{u}} (hZF : M.Models ZF)
local notation "I" => kpair_interpretation_l M (And.left hZF) (KP.exists_pair (ZF.modelsKP hZF))

theorem Fp_product_d.task_l {ω A P R n C S D κ : M.Domain} (h : Fp_product_d hZF ω A P R)
    (hw : M.IsOmega ω) (hn : M.mem n ω) (alphabet : Entry_d M n κ A) (stage : Fp_prefix_d hZF ω A n C S)
    {H : M.Domain → Prop} (generic : Generic_d M C S C H)
    (dense : Dense_set_d M P R P D) :
    ∃ m d q, M.mem m ω ∧ M.mem n m ∧ M.mem d D ∧ Fp_at_d I ω A m d ∧
      M.IsRestrictionOf I q d n ∧ H q := by
  let ρ : Env M 2 := ⟨fun i => [D,n].get i,fun _ => n⟩
  let φ : UnarySchema 2 := { body := .existsE (.conj (.mem .newest (.bound 2))
    (.conj (Formula.isRestriction kpair_convention_l (.bound 1) .newest (.bound 3))
      (.existsE (entry_m (.bound 4) .newest (.bound 1))))) }
  have sat q : φ.denote ρ q ↔ ∃ d, M.mem d D ∧ M.IsRestrictionOf I q d n ∧ ∃ s, Entry_d M n s d := by
    simp only [φ,UnarySchema.denote,Formula.satisfies_exists_iff,Formula.satisfies_conj_iff,
      Formula.satisfies_mem_iff,Formula.satisfies_isRestriction_iff I,entry_sat_l M hZF.1]
    rfl
  obtain ⟨E,members⟩ := ZF.separation_exists_d hZF φ ρ C
  have read q := (members q).trans (and_congr_right fun _ => sat q)
  have meet q (hq : M.mem q C) : ∃ s, M.mem s C ∧ Entry_d M s q S ∧ M.mem s E := by
    have fq := (stage.conditions q).mp hq
    obtain ⟨o,empty,ho⟩ := hw.1.1
    have seq := Structure.IsSequenceOfLength.empty I empty
    obtain ⟨n',succ,hn'⟩ := hw.1.2 n hn
    obtain ⟨t,ft,ending⟩ := fq.snoc_l hZF hw hn succ alphabet
      ⟨o,ho,seq.2.1,seq.2.2,fun i hi => (empty i hi).elim⟩
    have tp := (h.conditions t).mpr ⟨n',hn',ft⟩
    obtain ⟨d,dt,dD⟩ := dense.2 t tp (fun eq => KP.mem_irrefl_d (ZF.modelsKP hZF) P (eq ▸ tp))
    obtain ⟨m,hm,fd⟩ := (h.conditions d).mp dt.1
    have le₀ := ((h.order d t).mp dt.2.2).2.2
    have nm := le₀.domain_l I fd ft n succ.predecessor_mem
    have tq : Fp_le_d I t q := fun i a ia =>
      ⟨a,(ending.entries_l I hZF.1 fq.domain i a).mpr (Or.inl ia),fun _ h => h⟩
    have le := le₀.trans_l I tq
    obtain ⟨s,cut,fs⟩ := fd.restrict_l hZF (le.domain_l I fd fq)
    have hs := (stage.conditions s).mpr fs
    have sq : Fp_le_d I s q := by
      intro i a ia
      obtain ⟨b,ib,ab⟩ := le i a ia
      exact ⟨b,(cut.2 i b).mpr ⟨(fq.domain i).mpr ⟨a,ia⟩,ib⟩,ab⟩
    exact ⟨s,hs,(stage.order s q).mpr ⟨hs,hq,sq⟩,
      (read s).mpr ⟨hs,d,dD,cut,(fd.domain n).mp nm⟩⟩
  obtain ⟨p,hp⟩ := generic.inhabited
  obtain ⟨q,hq,qE⟩ := generic.meets p hp E (by
    intro s hs
    obtain ⟨t,ht,ts,tE⟩ := meet s hs.1
    exact ⟨t,⟨ht,fun eq => KP.mem_irrefl_d (ZF.modelsKP hZF) C (eq ▸ ht),ts⟩,tE⟩)
  obtain ⟨_,d,dD,cut,row⟩ := (read q).mp qE
  obtain ⟨m,hm,fd⟩ := (h.conditions d).mp (dense.1 d dD).1
  exact ⟨m,d,q,hm,(fd.domain n).mpr row,dD,fd,cut,hq⟩

end YesMetaZFC.Model.Forcing.Internal

/-! ## 原乘积泛型由各坐标滤子精确恢复

逐坐标接受原条件，即与每个原泛型条件逐行相容。实际共同加强和
地模型中的判定稠密集遂恢复原泛型成员关系；不对外部谓词作内部有限归纳。
-/
namespace YesMetaZFC.Model.Forcing.Internal
open SetTheory SetTheory.Definitional.Project
universe u
variable {M : Structure.{u}} (hZF : M.Models ZF)
local notation "I" => kpair_interpretation_l M (And.left hZF) (KP.exists_pair (ZF.modelsKP hZF))

theorem Fp_product_d.generic_rows_l {ω A P R q : M.Domain} {G : M.Domain → Prop}
    (product : Fp_product_d hZF ω A P R) (hw : M.IsOmega ω)
    (generic : Generic_d M P R P G) (hq : M.mem q P) :
    G q ↔ ∀ i a, Entry_d M i a q →
      ∃ p b, G p ∧ Entry_d M i b p ∧ M.MemberSubset a b := by
  constructor
  · exact fun gq i a ia => ⟨q,a,gq,ia,fun _ h => h⟩
  · intro rows
    apply (generic.mem_iff_compatible_l hZF (product.order_l hZF) hq).mpr
    intro p gp
    apply product.compatible_l hZF hw (generic.proper p gp).1 hq
    intro i a b ia ib
    obtain ⟨s,c,gs,ic,bc⟩ := rows i b ib
    obtain ⟨r,gr,rp,rs⟩ := generic.directed p s gp gs
    obtain ⟨m,_,fr⟩ := (product.conditions r).mp (generic.proper r gr).1
    obtain ⟨t,it,sa⟩ := ((product.order r p).mp rp).2.2 i a ia
    obtain ⟨u,iu,cu⟩ := ((product.order r s).mp rs).2.2 i c ic
    have bt : M.MemberSubset b t := fun z hz => fr.function.2 i u t iu it ▸ cu z (bc z hz)
    obtain ⟨_,_,_,_,ft⟩ := fr.coordinates i t it
    rintro k x y ⟨v,pair,hv⟩ ⟨w,pair',hw⟩
    exact ft.1.2 k x y ⟨v,pair,sa v hv⟩ ⟨w,pair',bt w hw⟩

/-- 在原 G 内选择严格超过指定前缀的稠密任务，供原泛型的有限历史使用。 -/
theorem Fp_product_d.task_in_generic_l {ω A P R n W D : M.Domain} {G : M.Domain → Prop}
    (product : Fp_product_d hZF ω A P R) (hw : M.IsOmega ω) (hn : M.mem n ω)
    (fa : M.IsSetFunctionFromTo I A ω W) (generic : Generic_d M P R P G)
    (dense : Dense_set_d M P R P D) :
    ∃ m d, M.mem m ω ∧ M.mem n m ∧ G d ∧ M.mem d D ∧ Fp_at_d I ω A m d := by
  obtain ⟨s,succ,hs⟩ := hw.1.2 n hn
  obtain ⟨C,S,stage⟩ := product.prefix_l hZF hs
  obtain ⟨a,ha,p,gp,pa⟩ := (product.project_generic_l hZF hw hs fa stage generic).inhabited
  have aP := ((stage.product_read_l hZF product hs).1 a).mp ha |>.1
  have ga := generic.upward p a gp aP ((product.order p a).mpr ⟨(generic.proper p gp).1,aP,pa⟩)
  obtain ⟨d,gd,dD,da⟩ := generic.meets_below_l hZF (product.order_l hZF) ga
    (fun q hq => dense.2 q hq.1 hq.2.1)
  obtain ⟨m,hm,fd⟩ := (product.conditions d).mp (generic.proper d gd).1
  have bound := ((product.order d a).mp da).2.2.domain_l I fd ((stage.conditions a).mp ha)
  exact ⟨m,d,hm,bound n succ.predecessor_mem,gd,dD,fd⟩

end YesMetaZFC.Model.Forcing.Internal
