import YesMetaZFC.SetTheory.Ord.Natural
import YesMetaZFC.SetTheory.FunctionConstruction
import YesMetaZFC.SetTheory.InnerModel.Recursion.Composition

/-! # 内部语法标签的有限序数码

固定构造符的标签由空集和有限次后继唯一确定。这里只编码宿主给出的有限标签；
公式长度、变量编号和递归指标仍是模型自身 ω 的元素，不要求它们外部标准。
-/

namespace YesMetaZFC.SetTheory.Internal
open Definitional.Project
universe u
variable {M : Structure.{u}}

def Num_d : Nat → M.Domain → Prop
  | 0, x => ∀ y, ¬ M.mem y x
  | n+1, x => ∃ y, Num_d n y ∧ M.SuccessorOf x y

def num_m : (k : Nat) → {n : Nat} → Term n → Formula 1 n
  | 0, _, x => Formula.isEmpty x
  | k+1, _, x => .existsE (.conj (num_m k .newest) (Formula.isSuccessor x.weaken .newest))

@[simp] theorem num_closed_l (k : Nat) {n} (x : Term n) (hx : x.freeSupport = []) :
    (num_m k x).FreeClosed := by
  induction k generalizing n with
  | zero => exact Formula.isEmpty_freeClosed x hx
  | succ k ih =>
    simp only [num_m, Definitional.Formula.FreeClosed]
    exact ⟨ih .newest rfl, Formula.isSuccessor_freeClosed _ _ (by simpa using hx) rfl⟩

theorem num_sat_l (k : Nat) {n} (ρ : Env M n) (x : Term n) :
    Formula.satisfies ρ (num_m k x) ↔ Num_d k (x.eval ρ) := by
  induction k generalizing n with
  | zero => exact Formula.satisfies_isEmpty_iff ρ x
  | succ k ih =>
    simp only [num_m, Num_d, Formula.satisfies_exists_iff, Formula.satisfies_conj_iff,
      ih, Formula.satisfies_isSuccessor_iff, Definitional.Term.eval_weaken, Definitional.Term.eval_newest]

theorem num_exists_l (hKP : M.Models KP) (k : Nat) : ∃ x : M.Domain, Num_d k x := by
  induction k with
  | zero => exact KP.exists_empty hKP
  | succ k ih =>
    obtain ⟨x, hx⟩ := ih
    obtain ⟨y, hy⟩ := KP.exists_successor hKP x
    exact ⟨y, x, hx, hy⟩

theorem num_unique_l (hE : Extensional M) {k} {x y : M.Domain} (hx : Num_d k x) (hy : Num_d k y) : x = y := by
  induction k generalizing x y with
  | zero => exact hE.eq_of_same_members x y (fun a => ⟨fun h => (hx a h).elim, fun h => (hy a h).elim⟩)
  | succ k ih =>
    obtain ⟨a, ha, hxa⟩ := hx
    obtain ⟨b, hb, hyb⟩ := hy
    have he := ih ha hb
    subst b
    exact hE.eq_of_same_members x y (fun a => (hxa a).trans (hyb a).symm)

theorem num_lt_l (hE : Extensional M) {k l x y} (hx : Num_d k x) (hy : Num_d l y)
    (h : k < l) : M.mem x y := by
  induction l generalizing y with
  | zero => omega
  | succ l ih =>
    obtain ⟨a, ha, hya⟩ := hy
    by_cases hk : k = l
    · subst k
      exact (num_unique_l hE ha hx) ▸ hya.predecessor_mem
    · exact (hya x).mpr (Or.inl (ih ha (by omega)))

theorem num_injective_l (hKP : M.Models KP) {k l} {x : M.Domain} (hk : Num_d k x) (hl : Num_d l x) : k = l := by
  apply Classical.byContradiction
  intro h
  have he : M.mem x x := by
    rcases Nat.lt_or_gt_of_ne h with h | h
    · exact num_lt_l hKP.1 hk hl h
    · exact num_lt_l hKP.1 hl hk h
  exact KP.mem_irrefl_d hKP x he

theorem num_mem_l (hE : Extensional M) {ω k x} (hω : M.IsOmega ω) (hx : Num_d k x) : M.mem x ω := by
  induction k generalizing x with
  | zero =>
    obtain ⟨e, he, heω⟩ := hω.1.1
    exact num_unique_l hE (k := 0) he hx ▸ heω
  | succ k ih =>
    obtain ⟨a, ha, hxa⟩ := hx
    obtain ⟨y, hya, hyω⟩ := hω.1.2 a (ih ha)
    have he := hE.eq_of_same_members y x (fun z => (hya z).trans (hxa z).symm)
    exact he ▸ hyω

end YesMetaZFC.SetTheory.Internal

/-! ## 地模型内的集合结构编码

结构码是有序对 (X,R)，其中 X 非空而 R⊆X×X。解码载体是实际子类型，关系
从模型内图逐点读取；不选择载体基点，也不假设解码结构满足外延性或 ZFC。
-/

namespace YesMetaZFC.SetTheory.Internal
open Definitional.Project
universe u
variable {M : Structure.{u}} {𝒞 : OrderedPairConvention} (I : 𝒞.Interpretation M)

def Smdl_d (c X R : M.Domain) : Prop :=
  I.Codes c X R ∧ (∃ x, M.mem x X) ∧ M.IsSetRelationOn I R X

def smdl_m {n} (c X R : Term n) : Formula 1 n :=
  .conj (𝒞.code c X R) (.conj (.existsE (.mem .newest X.weaken))
    (.conj (Formula.isRelation 𝒞 R) (.forallE (.forallE
      (.imp (Formula.orderedPairMem 𝒞 (.bound 1) .newest R.weaken.weaken)
        (.conj (.mem (.bound 1) X.weaken.weaken) (.mem .newest X.weaken.weaken)))))))
derive_free_closed smdl_m

theorem smdl_sat_l {n} (ρ : Env M n) (c X R : Term n) :
    Formula.satisfies ρ (smdl_m (𝒞 := 𝒞) c X R) ↔ Smdl_d I (c.eval ρ) (X.eval ρ) (R.eval ρ) := by
  simp only [smdl_m, Smdl_d, Formula.satisfies_conj_iff, I.satisfies_code_iff,
    Formula.satisfies_exists_iff, Formula.satisfies_mem_iff, Formula.satisfies_forall_iff,
    Formula.satisfies_imp_iff, Formula.satisfies_isRelation_iff I, Formula.satisfies_orderedPairMem_iff I,
    Definitional.Term.eval_newest, Definitional.Term.eval_weaken]
  rfl

/-- 编码结构的外部解码与地模型同层，不从非空性消去出 Type 数据。 -/
def smdl_structure_l {X R : M.Domain} (hX : ∃ x, M.mem x X) : Structure.{u} where
  Domain := {x : M.Domain // M.mem x X}
  nonempty := hX.elim (fun x hx => ⟨⟨x, hx⟩⟩)
  mem x y := M.PairMember I x.val y.val R

theorem smdl_unique_l {c X R Y S} (h : Smdl_d I c X R) (k : Smdl_d I c Y S) : X = Y ∧ R = S :=
  I.injective h.1 k.1

/-- 在非空集合上，任意实际二元公式都生成内部关系结构及精确解释证书。 -/
theorem smdl_exists_l (hZF : M.Models ZF) {n} (φ : BinarySchema n) (ρ : Env M n)
    {X} (hX : ∃ x, M.mem x X) : ∃ c R, Smdl_d I c X R ∧
      ∀ x y, M.PairMember I x y R ↔ M.mem x X ∧ M.mem y X ∧ φ.denote ρ x y := by
  obtain ⟨R, hR, hr⟩ := ZF.exists_setRelationOn_of_denote hZF I φ ρ X
  obtain ⟨c, hc⟩ := I.total X R
  exact ⟨c, R, ⟨hc, hX, hR⟩, hr⟩

/-- 任意非空模型内集合的诱导隶属结构，直接作为编码设施的实际实例。 -/
theorem smdl_membership_l (hZF : M.Models ZF) {X} (hX : ∃ x, M.mem x X) :
    ∃ c R, Smdl_d I c X R ∧ ∀ x y,
      M.PairMember I x y R ↔ M.mem x X ∧ M.mem y X ∧ M.mem x y := by
  let φ : BinarySchema 0 := { body := .mem (.bound 1) .newest }
  simpa only [BinarySchema.denote, φ, Formula.satisfies_mem_iff,
    Definitional.Term.eval_newest, Term.eval_bound_one_push, Term.eval_bound_zero_push] using
    smdl_exists_l I hZF φ ⟨Fin.elim0, fun _ => X⟩ hX

end YesMetaZFC.SetTheory.Internal

/-! ## 集合关系的规范商及下降映射

等价类由分离形成，全部类由替换收集。泛性质直接构造唯一的内部函数图，
不选择代表元，也不引入对象层选择公理。
-/
namespace YesMetaZFC.SetTheory.Internal
open Definitional.Project InnerModel
universe u
variable {M : Structure.{u}}

structure Qt_equiv_d (A E : M.Domain) : Prop where
  refl : ∀ x, M.mem x A → Rd_entry_d x x E
  symm : ∀ x y, Rd_entry_d x y E → Rd_entry_d y x E
  trans : ∀ x y z, Rd_entry_d x y E → Rd_entry_d y z E → Rd_entry_d x z E

def Qt_class_d (A E x B : M.Domain) : Prop := ∀ y, M.mem y B ↔ M.mem y A ∧ Rd_entry_d x y E

def qt_class_m {d} (A E x B : Term d) : Formula 1 d := .forallE (.iff (.mem .newest B.weaken)
  (.conj (.mem .newest A.weaken) (rd_entry_m x.weaken .newest E.weaken)))
derive_free_closed qt_class_m

theorem qt_class_sat_l (hE : Extensional M) {d} (ρ : Env M d) (A E x B : Term d) :
    Formula.satisfies ρ (qt_class_m A E x B) ↔ Qt_class_d (A.eval ρ) (E.eval ρ) (x.eval ρ) (B.eval ρ) := by
  simp only [qt_class_m, Qt_class_d, Formula.satisfies_forall_iff, Formula.satisfies_iff_iff,
    Formula.satisfies_mem_iff, Formula.satisfies_conj_iff, rd_entry_sat_l hE, Definitional.Term.eval_weaken]; rfl

structure Qt_map_d (A E q C : M.Domain) : Prop where
  function : Fn0_d A C q
  range : ∀ B, M.mem B C ↔ ∃ x, Rd_entry_d x B q
  classes : ∀ x B, Rd_entry_d x B q ↔ M.mem x A ∧ Qt_class_d A E x B

theorem qt_map_exists_l (hZF : M.Models ZF) (A E : M.Domain) : ∃ q C, Qt_map_d A E q C := by
  let I := kp_pair_l (ZF.modelsKP hZF)
  let ρ : Env M 2 := (⟨fun _ => A, fun _ => A⟩ : Env M 1).push E
  let φ : BinarySchema 2 := { body := qt_class_m (.bound 3) (.bound 2) (.bound 1) .newest }
  have sat x B : φ.denote ρ x B ↔ Qt_class_d A E x B := qt_class_sat_l hZF.1 _ _ _ _ _
  obtain ⟨P, hP⟩ := ZF.exists_powerSet hZF A
  obtain ⟨q, hq, hq'⟩ := ZF.exists_setFunctionFromTo_of_denote hZF I φ ρ (source := A) (target := P)
    (by
      intro x _
      let ψ : UnarySchema 2 := { body := rd_entry_m (.bound 1) .newest (.bound 2) }
      obtain ⟨B, hB⟩ := ZF.separation_exists_d hZF ψ ⟨Fin.cases x (fun _ => E), fun _ => A⟩ A
      exact ⟨B, (sat x B).mpr fun y => (hB y).trans (and_congr_right fun _ => rd_entry_sat_l hZF.1 _ _ _ _)⟩)
    (fun x _ B C hB hC => hZF.1.eq_of_same_members B C fun y => ((sat x B).mp hB y).trans ((sat x C).mp hC y).symm)
    (fun x B _ hB => (hP B).mpr fun y hy => (((sat x B).mp hB y).mp hy).1)
  obtain ⟨C, hC⟩ := ZF.exists_range_of_setFunction hZF I hq.1 hq.2.1
  have fn : M.IsSetFunctionFromTo I q A C := ⟨hq.1, hq.2.1,
    fun x hx => (hq.2.2 x hx).imp fun B hB => ⟨(hC B).mpr ⟨x, hB.2⟩, hB.2⟩⟩
  exact ⟨q, C, fn0_of_function_l (ZF.modelsKP hZF) fn, hC,
    fun x B => (hq' x B).trans (and_congr_right fun _ => sat x B)⟩

theorem Qt_map_d.kernel_l (hE : Extensional M) {A E q C x y B D : M.Domain}
    (h : Qt_map_d A E q C) (he : Qt_equiv_d A E) (hx : Rd_entry_d x B q) (hy : Rd_entry_d y D q) :
    B = D ↔ Rd_entry_d x y E := by
  obtain ⟨hxA, hB⟩ := (h.classes x B).mp hx
  obtain ⟨hyA, hD⟩ := (h.classes y D).mp hy
  refine ⟨fun e => ((hB y).mp (e.symm ▸ (hD y).mpr ⟨hyA, he.refl y hyA⟩)).2, fun hxy => ?_⟩
  apply hE.eq_of_same_members B D
  intro z
  exact (hB z).trans ((and_congr_right fun _ =>
    ⟨he.trans y x z (he.symm x y hxy), he.trans x y z hxy⟩).trans (hD z).symm)

/-- 任何在等价类上为常值的实际函数，都唯一地通过商映射分解。 -/
theorem qt_descend_l (hZF : M.Models ZF) {A q C Y f : M.Domain} (hq : Fn0_d A C q)
    (hr : ∀ B, M.mem B C → ∃ x, Rd_entry_d x B q) (hf : Fn0_d A Y f)
    (hc : ∀ x y B u v, Rd_entry_d x B q → Rd_entry_d y B q →
      Rd_entry_d x u f → Rd_entry_d y v f → u = v) :
    ∃ g, Fn0_d C Y g ∧ (∀ x B y, Rd_entry_d x B q → Rd_entry_d x y f → Rd_entry_d B y g) ∧
      ∀ k, Fn0_d C Y k → (∀ x B y, Rd_entry_d x B q → Rd_entry_d x y f → Rd_entry_d B y k) → k = g := by
  let I := kp_pair_l (ZF.modelsKP hZF)
  let ρ : Env M 2 := (⟨fun _ => q, fun _ => q⟩ : Env M 1).push f
  let φ : BinarySchema 2 := { body := .existsE (.conj (rd_entry_m .newest (.bound 2) (.bound 4))
    (rd_entry_m .newest (.bound 1) (.bound 3))) }
  have sat B y : φ.denote ρ B y ↔ ∃ x, Rd_entry_d x B q ∧ Rd_entry_d x y f := by
    simp only [φ, BinarySchema.denote, Formula.satisfies_exists_iff, Formula.satisfies_conj_iff,
      rd_entry_sat_l hZF.1]; rfl
  obtain ⟨g, hg, spec⟩ := ZF.exists_setFunctionFromTo_of_denote hZF I φ ρ (source := C) (target := Y)
    (fun B hB => by
      obtain ⟨x, hx⟩ := hr B hB
      obtain ⟨y, _, hxy⟩ := hf.2.1 x (hq.bound_l hx).1
      exact ⟨y, (sat B y).mpr ⟨x, hx, hxy⟩⟩)
    (fun B _ u v hu hv => by
      obtain ⟨x, hx, hxu⟩ := (sat B u).mp hu
      obtain ⟨y, hy, hyv⟩ := (sat B v).mp hv
      exact hc x y B u v hx hy hxu hyv)
    (fun B y _ hy => ((sat B y).mp hy).elim fun _ hx => (hf.bound_l hx.2).2)
  have fn := fn0_of_function_l (ZF.modelsKP hZF) hg
  have law x B y (hx : Rd_entry_d x B q) (hy : Rd_entry_d x y f) : Rd_entry_d B y g :=
    (spec B y).mpr ⟨(hq.bound_l hx).2, (sat B y).mpr ⟨x, hx, hy⟩⟩
  refine ⟨g, fn, law, fun k hk hkq => hk.ext_l hZF.1 fn ?_⟩
  intro B hB
  obtain ⟨x, hx⟩ := hr B hB
  obtain ⟨y, _, hy⟩ := hf.2.1 x (hq.bound_l hx).1
  exact ⟨y, hkq x B y hx hy, law x B y hx hy⟩

end YesMetaZFC.SetTheory.Internal
