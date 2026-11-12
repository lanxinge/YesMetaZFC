import YesMetaZFC.Model.Forcing.Stage.AntichainDense
import YesMetaZFC.Model.Forcing.Functions.Surjection
import YesMetaZFC.SetTheory.DependentChoice
import YesMetaZFC.SetTheory.Card.CountableUnion
import YesMetaZFC.SetTheory.Card.InfiniteBound
import YesMetaZFC.SetTheory.Card.BoundedComparison
import YesMetaZFC.Model.Forcing.Stage.AntichainRefine
import YesMetaZFC.SetTheory.FunctionRetraction
import YesMetaZFC.SetTheory.Descriptive.Tree.RetractionFixed
import YesMetaZFC.SetTheory.Descriptive.Topology.Topology
import YesMetaZFC.Model.Forcing.Boolean.DenseMap

/-! # 坍缩名字的内部判值反链

每个旧输入对应一张实际极大反链，反链元素决定同一原函数名字的旧输出。
整族由原选择公理统一成原模型内函数图，不以宿主 ω 列替代内部 ω。
-/
namespace YesMetaZFC.Model.Forcing.Internal
open SetTheory SetTheory.Definitional.Project
universe u
variable {M : Structure.{u}}

def Ac_decide_d (B R z b f p X i A : M.Domain) : Prop := Antichain_d M B R z A ∧
  (∀ a, M.mem a A → Below_d M B R z a p ∧ ∃ x, M.mem x X ∧ Old_value_d M B R z b f a i x) ∧
  ∀ q, Below_d M B R z q p → ∃ a, M.mem a A ∧ Cmp_d M B R z q a

def ac_decide_m {n} (B R z b f p X i A : Term n) : Formula 1 n := set[n] ⟪
  ⌜antichain_m⌝ₚ(⌜B⌝ₛ,⌜R⌝ₛ,⌜z⌝ₛ,⌜A⌝ₛ) ∧
  (∀ a ∈ ⌜A⌝ₛ, ⌜below_m⌝ₚ(⌜B⌝ₛ,⌜R⌝ₛ,⌜z⌝ₛ,a,⌜p⌝ₛ) ∧
    (∃ x ∈ ⌜X⌝ₛ, ⌜old_value_m⌝ₚ(⌜B⌝ₛ,⌜R⌝ₛ,⌜z⌝ₛ,⌜b⌝ₛ,⌜f⌝ₛ,a,⌜i⌝ₛ,x))) ∧
  (∀ q, ⌜below_m⌝ₚ(⌜B⌝ₛ,⌜R⌝ₛ,⌜z⌝ₛ,q,⌜p⌝ₛ) →
    ∃ a ∈ ⌜A⌝ₛ, ⌜cmp_m⌝ₚ(⌜B⌝ₛ,⌜R⌝ₛ,⌜z⌝ₛ,q,a))⟫
derive_free_closed ac_decide_m

theorem ac_decide_sat_l (hE : Extensional M) {n} (ρ : Env M n) (B R z b f p X i A : Term n) :
    Formula.satisfies ρ (ac_decide_m B R z b f p X i A) ↔
      Ac_decide_d (B.eval ρ) (R.eval ρ) (z.eval ρ) (b.eval ρ) (f.eval ρ) (p.eval ρ) (X.eval ρ) (i.eval ρ) (A.eval ρ) := by
  simp only [ac_decide_m,Ac_decide_d,Formula.satisfies_conj_iff,Formula.satisfies_forallMem_iff,
    Formula.satisfies_existsMem_iff,Formula.satisfies_forall_iff,Formula.satisfies_imp_iff,
    antichain_sat_l M hE,below_sat_l M hE,cmp_sat_l M hE,old_value_sat_l hE,Definitional.Term.eval_weaken]
  rfl

variable (hZFC : M.Models ZFC) {B R z a b T w f D X : M.Domain} (O : Cond_order_d M B R z)
local notation "hZF" => ZFC.models_zf_l hZFC
local notation "I" => kpair_interpretation_l M (And.left hZFC) (KP.exists_pair (ZF.modelsKP hZF))
include hZFC O

theorem old_value_antichain_l (name : Fn_name_d M B R z a T w f)
    (hb : M.mem b B) (ha : Below_d M B R z a b) (hT : Check_d M b D T) (hw : Check_d M b X w)
    {p i : M.Domain} (hp : Below_d M B R z p a) (hi : M.mem i D) :
    ∃ A, Ac_decide_d B R z b f p X i A := by
  let ρ : Env M 7 := ⟨fun j => [B,R,z,b,f,i,X].get j,fun _ => b⟩
  let φ : UnarySchema 7 := { body := .existsE (.conj (.mem .newest (.bound 8))
    (old_value_m (.bound 2) (.bound 3) (.bound 4) (.bound 5) (.bound 6) (.bound 1) (.bound 7) .newest)) }
  obtain ⟨E,members⟩ := ZF.separation_exists_d hZF φ ρ B
  have member q : M.mem q E ↔ M.mem q B ∧ ∃ x, M.mem x X ∧ Old_value_d M B R z b f q i x := by
    apply (members q).trans (and_congr_right fun _ => ?_)
    simp only [φ,Formula.satisfies_exists_iff,Formula.satisfies_conj_iff,Formula.satisfies_mem_iff,old_value_sat_l hZFC.1]
    rfl
  have dense := old_value_dense_l O hZF name hb ha hT hw hi
  obtain ⟨A,antichain,bound,maximal⟩ := antichain_dense_l hZFC O hp.1 (D := E) (by
    intro q hq
    obtain ⟨r,hr,value⟩ := dense q (below_trans_l O ha.1 hq hp)
    exact ⟨r,hr,(member r).mpr ⟨hr.1,value⟩⟩)
  exact ⟨A,antichain,(fun q hq => ⟨(bound q hq).2,((member q).mp (bound q hq).1).2⟩),maximal⟩

theorem old_value_antichains_l (name : Fn_name_d M B R z a T w f)
    (hb : M.mem b B) (ha : Below_d M B R z a b) (hT : Check_d M b D T) (hw : Check_d M b X w)
    {p : M.Domain} (hp : Below_d M B R z p a) :
    ∃ P H, M.IsPowerSetOf P B ∧ M.IsSetFunctionFromTo I H D P ∧
      ∀ i A, Entry_d M i A H → Ac_decide_d B R z b f p X i A := by
  obtain ⟨P,power⟩ := ZF.exists_powerSet hZF B
  let ρ : Env M 7 := ⟨fun j => [B,R,z,b,f,p,X].get j,fun _ => b⟩
  let φ : BinarySchema 7 := {
    body := ac_decide_m (.bound 2) (.bound 3) (.bound 4) (.bound 5) (.bound 6) (.bound 7) (.bound 8) (.bound 1) .newest }
  have sat i A : φ.denote ρ i A ↔ Ac_decide_d B R z b f p X i A := ac_decide_sat_l hZFC.1 ..
  obtain ⟨H,fn,values⟩ := ZFC.uniformize_formula_l I hZFC φ ρ (X := D) (Y := P) (fun i hi => by
    obtain ⟨A,hA⟩ := old_value_antichain_l hZFC O name hb ha hT hw hp hi
    exact ⟨A,(power A).mpr (fun q hq => (hA.1.1 q hq).1),(sat i A).mpr hA⟩)
  exact ⟨P,H,power,fn,fun i A ia => (sat i A).mp (values i A ia)⟩

end YesMetaZFC.Model.Forcing.Internal

/-! ## 判值反链的标签覆盖与坍缩的反链下界

每行判值反链的标签覆盖该输入的全部可能旧输出。满射性使各行标签覆盖
整个目标集；因此不能用同一个较小无限基数界住全部局部反链。
-/
namespace YesMetaZFC.Model.Forcing.Internal
open SetTheory SetTheory.Definitional.Project
universe u
variable {M : Structure.{u}} (hZF : M.Models ZF) {B R z a b T w f D X : M.Domain} (O : Cond_order_d M B R z)
local notation "I" => kpair_interpretation_l M (And.left hZF) (KP.exists_pair (ZF.modelsKP hZF))
include O

theorem Ac_decide_d.label_l {p i A : M.Domain} (row : Ac_decide_d B R z b f p X i A)
    (name : Fn_name_d M B R z a T w f) (hb : M.mem b B) (ha : Below_d M B R z a b)
    (hp : Below_d M B R z p a) : ∃ F, M.IsSetFunctionFromTo I F A X ∧
      (∀ q x, Entry_d M q x F ↔ M.mem q A ∧ M.mem x X ∧ Old_value_d M B R z b f q i x) ∧
      ∀ q x, Below_d M B R z q p → Old_value_d M B R z b f q i x → ∃ r, M.mem r A ∧ Entry_d M r x F := by
  let ρ : Env M 7 := ⟨fun j => [B,R,z,b,f,i,X].get j,fun _ => b⟩
  let φ : BinarySchema 7 := {
    body := .conj (.mem .newest (.bound 8))
      (old_value_m (.bound 2) (.bound 3) (.bound 4) (.bound 5) (.bound 6) (.bound 1) (.bound 7) .newest) }
  have sat q x : φ.denote ρ q x ↔ M.mem x X ∧ Old_value_d M B R z b f q i x := by
    simp only [φ,BinarySchema.denote,Formula.satisfies_conj_iff,Formula.satisfies_mem_iff,old_value_sat_l hZF.1]
    rfl
  obtain ⟨F,fn,values⟩ := ZF.exists_setFunctionFromTo_of_denote hZF I φ ρ (source := A) (target := X)
    (fun q hq => ((row.2.1 q hq).2).imp fun x hx => (sat q x).mpr hx)
    (fun q hq x y hx hy => old_value_unique_l O hZF name ha.1 hb
      (below_trans_l O ha.1 (row.2.1 q hq).1 hp)
      (below_trans_l O hb (below_trans_l O ha.1 (row.2.1 q hq).1 hp) ha)
      ((sat q x).mp hx).2 ((sat q y).mp hy).2)
    (fun q x _ hx => ((sat q x).mp hx).1)
  have graph q x : Entry_d M q x F ↔ M.mem q A ∧ M.mem x X ∧ Old_value_d M B R z b f q i x :=
    (values q x).trans (and_congr_right fun _ => sat q x)
  refine ⟨F,fn,graph,fun q x hq value => ?_⟩
  obtain ⟨r,hr,s,hs,sr⟩ := row.2.2 q hq
  obtain ⟨y,hy,ry⟩ := fn.2.2 r hr
  have sr' : Below_d M B R z s r := ⟨hs.1,hs.2.1,sr⟩
  have sa := below_trans_l O ha.1 (below_trans_l O hp.1 hs hq) hp
  have eq := old_value_unique_l O hZF name ha.1 hb sa (below_trans_l O hb sa ha)
    (old_value_lower_l O hZF hb name.2.2.1 q s hq.1 hs value)
    (old_value_lower_l O hZF hb name.2.2.1 r s (row.1.1 r hr).1 sr' ((graph r y).mp ry).2.2)
  exact ⟨r,hr,eq.symm ▸ ry⟩

variable (hZFC : M.Models ZFC)
include hZFC

/-- 源集与每行反链均不超过 μ 时，被迫满射的旧目标也不超过 μ。 -/
theorem onto_antichains_bound_l {ω μ p P H : M.Domain} (hω : M.IsOmega ω) (hμ : M.IsInfiniteCardinal I ω μ)
    (name : Onto_name_d B R z a T w f) (hb : M.mem b B) (ha : Below_d M B R z a b)
    (hT : Check_d M b D T) (hw : Check_d M b X w) (hp : Below_d M B R z p a)
    (source : M.CardinalLessOrEqual I D μ) (rows : M.IsSetFunctionFromTo I H D P)
    (decide : ∀ i A, Entry_d M i A H → Ac_decide_d B R z b f p X i A)
    (sizes : ∀ i A, Entry_d M i A H → M.CardinalLessOrEqual I A μ) : M.CardinalLessOrEqual I X μ := by
  let ρ : Env M 6 := ⟨fun j => [B,R,z,b,f,p].get j,fun _ => b⟩
  let φ : BinarySchema 6 := { body := set[8] ⟪∃ q,
    ⌜below_m⌝ₚ(⌜(.bound 2 : Term 8)⌝ₛ,⌜(.bound 3 : Term 8)⌝ₛ,⌜(.bound 4 : Term 8)⌝ₛ,q,⌜(.bound 7 : Term 8)⌝ₛ) ∧
    ⌜old_value_m⌝ₚ(⌜(.bound 2 : Term 8)⌝ₛ,⌜(.bound 3 : Term 8)⌝ₛ,⌜(.bound 4 : Term 8)⌝ₛ,
      ⌜(.bound 5 : Term 8)⌝ₛ,⌜(.bound 6 : Term 8)⌝ₛ,q,⌜(.bound 1 : Term 8)⌝ₛ,⌜(.newest : Term 8)⌝ₛ)⟫ }
  have sat i x : φ.denote ρ i x ↔ ∃ q, Below_d M B R z q p ∧ Old_value_d M B R z b f q i x := by
    simp only [φ,BinarySchema.denote,Formula.satisfies_exists_iff,Formula.satisfies_conj_iff,
      below_sat_l M hZF.1,old_value_sat_l hZF.1,Definitional.Term.eval_weaken]
    rfl
  obtain ⟨W,product⟩ := ZF.exists_cartesianProduct hZF I μ μ
  have bound : M.CardinalLessOrEqual I X W := ZFC.cover_bound_l I hZFC φ ρ source product (by
    intro i hi Y member
    obtain ⟨A,_,ia⟩ := rows.2.2 i hi
    obtain ⟨F,fn,graph,cover⟩ := (decide i A ia).label_l hZF O name.1 hb ha hp
    have typed : M.IsSetFunctionFromTo I F A Y := ⟨fn.1,fn.2.1,fun q hq => by
      obtain ⟨x,hx,qx⟩ := fn.2.2 q hq
      exact ⟨x,(member x).mpr ⟨hx,(sat i x).mpr ⟨q,((decide i A ia).2.1 q hq).1,((graph q x).mp qx).2.2⟩⟩,qx⟩⟩
    have onto : M.IsSetSurjectiveOnto I F A Y := by
      intro x hx
      obtain ⟨q,hq,value⟩ := (sat i x).mp ((member x).mp hx).2
      exact cover q x hq value
    obtain ⟨j,hj⟩ := ZFC.surjection_bound_l I hZFC typed onto
    obtain ⟨k,hk⟩ := sizes i A ia
    exact ZF.exists_compositionInjection hZF I hj hk) (by
    intro x hx
    obtain ⟨q,hq,i,hi,value⟩ := onto_old_dense_l O hZF name hb ha hT hw hx p hp
    exact ⟨i,hi,(sat i x).mpr ⟨q,hq,value⟩⟩)
  obtain ⟨id,hid⟩ := ZF.exists_identityBijection hZF I μ
  obtain ⟨j,hj⟩ := ZF.infinite_product_l I hZF hω hμ ⟨id,hid.1⟩ ⟨id,hid.1⟩ product
  obtain ⟨k,hk⟩ := bound
  exact ZF.exists_compositionInjection hZF I hk hj

/-- 真正坍缩的每个正锥都有超出任意固定较小无限基数界的实际内部反链。 -/
theorem onto_antichain_unbounded_l {ω μ p : M.Domain} (hω : M.IsOmega ω) (hμ : M.IsInfiniteCardinal I ω μ)
    (name : Onto_name_d B R z a T w f) (hb : M.mem b B) (ha : Below_d M B R z a b)
    (hT : Check_d M b D T) (hw : Check_d M b X w) (hp : Below_d M B R z p a)
    (source : M.CardinalLessOrEqual I D μ) (large : ¬ M.CardinalLessOrEqual I X μ) :
    ∃ A, Antichain_d M B R z A ∧ (∀ q, M.mem q A → Below_d M B R z q p) ∧ ¬ M.CardinalLessOrEqual I A μ := by
  classical
  obtain ⟨P,H,_,rows,decide⟩ := old_value_antichains_l hZFC O name.1 hb ha hT hw hp
  apply Classical.byContradiction
  intro no
  apply large
  exact onto_antichains_bound_l hZF O hZFC hω hμ name hb ha hT hw hp source rows decide (by
    intro i A ia
    apply Classical.byContradiction
    intro largeA
    exact no ⟨A,(decide i A ia).1,fun q hq => ((decide i A ia).2.1 q hq).1,largeA⟩)

end YesMetaZFC.Model.Forcing.Internal

/-! ## 坍缩的每个正锥都有目标基数大小的反链

若某行判值反链已足够大，直接取它。否则先取可数个互不相容的正锥，
在第 i 个锥内取足以容纳第 i 行的反链，再取并。标签覆盖排除这个并仍然小。
该证明包含奇异基数情形，不使用目标基数的正则性。
-/
namespace YesMetaZFC.Model.Forcing.Internal
open SetTheory SetTheory.Definitional.Project
universe u
variable {M : Structure.{u}} (hZFC : M.Models ZFC)
local notation "hZF" => ZFC.models_zf_l hZFC
local notation "I" => kpair_interpretation_l M (And.left hZFC) (KP.exists_pair (ZF.modelsKP hZF))

theorem collapse_antichain_l {B R z a b T w f ω κ p : M.Domain} (O : Cond_order_d M B R z)
    (hω : M.IsOmega ω) (hκ : M.IsUncountableCardinal I ω κ) (size : M.CardinalLessOrEqual I B κ)
    (name : Onto_name_d B R z a T w f) (hb : M.mem b B) (ha : Below_d M B R z a b)
    (hT : Check_d M b ω T) (hw : Check_d M b κ w) (hp : Below_d M B R z p a) :
    ∃ A F, Antichain_d M B R z A ∧ (∀ q, M.mem q A → Below_d M B R z q p) ∧
      M.IsSetBijectionFromTo I F κ A := by
  classical
  have trans {X Y Z : M.Domain} (xy : M.CardinalLessOrEqual I X Y) (yz : M.CardinalLessOrEqual I Y Z) :
      M.CardinalLessOrEqual I X Z := by
    obtain ⟨F,fn⟩ := xy
    obtain ⟨G,gn⟩ := yz
    exact ZF.exists_compositionInjection hZF I fn gn
  have small {A} (hA : Antichain_d M B R z A) : M.CardinalLessOrEqual I A κ :=
    trans (ZF.exists_inclusionInjection hZF I (fun q hq => (hA.1 q hq).1)) size
  have finish {A} (anti : Antichain_d M B R z A) (below : ∀ q, M.mem q A → Below_d M B R z q p)
      (large : M.CardinalLessOrEqual I κ A) :
      ∃ A F, Antichain_d M B R z A ∧ (∀ q, M.mem q A → Below_d M B R z q p) ∧ M.IsSetBijectionFromTo I F κ A := by
    obtain ⟨F,fn⟩ := ZF.equinumerous_of_cardinalLessOrEqual hZF I large (small anti)
    exact ⟨A,F,anti,below,fn⟩
  obtain ⟨P,H,power,rows,decide⟩ := old_value_antichains_l hZFC O name.1 hb ha hT hw hp
  by_cases big : ∃ i A, Entry_d M i A H ∧ M.CardinalLessOrEqual I κ A
  · obtain ⟨i,A,ia,large⟩ := big
    exact finish (decide i A ia).1 (fun q hq => ((decide i A ia).2.1 q hq).1) large
  have noBig i A (ia : Entry_d M i A H) : ¬ M.CardinalLessOrEqual I κ A := fun large => big ⟨i,A,ia,large⟩
  obtain ⟨id,hid⟩ := ZF.exists_identityBijection hZF I ω
  have infω : M.IsInfiniteCardinal I ω ω := ⟨ZF.omega_cardinal_l I hZF hω,id,hid.1⟩
  obtain ⟨S,antiS,belowS,uncountable⟩ := onto_antichain_unbounded_l hZF O hZFC hω infω name hb ha hT hw hp
    ⟨id,hid.1⟩ (ZF.cardinal_not_le_member_l I hZF hκ.1 hκ.2)
  have ωκ := ZF.exists_inclusionInjection hZF I (hκ.1.1.transitive ω hκ.2)
  obtain ⟨E,enumeration⟩ := (ZF.bounded_compare_l I hZF hκ.1.1 ωκ (small antiS)).resolve_right uncountable
  -- 在互不相容的锥内分别放大各行，所有选择由一个内部函数图统一。
  let ρ : Env M 5 := ⟨fun i => [B,R,z,E,H].get i,fun _ => b⟩
  let φ : BinarySchema 5 := { body := set[7] ⟪∃ q, ∃ A,
    ⌜entry_m⌝ₚ(⌜(.bound 1 : Term 7)⌝ₛ,q,⌜(.bound 5 : Term 7)⌝ₛ) ∧
    ⌜entry_m⌝ₚ(⌜(.bound 1 : Term 7)⌝ₛ,A,⌜(.bound 6 : Term 7)⌝ₛ) ∧
    ⌜antichain_m⌝ₚ(⌜(.bound 2 : Term 7)⌝ₛ,⌜(.bound 3 : Term 7)⌝ₛ,⌜(.bound 4 : Term 7)⌝ₛ,⌜(.newest : Term 7)⌝ₛ) ∧
    (∀ r ∈ ⌜(.newest : Term 7)⌝ₛ, ⌜below_m⌝ₚ(⌜(.bound 2 : Term 7)⌝ₛ,⌜(.bound 3 : Term 7)⌝ₛ,⌜(.bound 4 : Term 7)⌝ₛ,r,q)) ∧
    ⌜(Formula.cardinalLessOrEqual kpair_convention_l)⌝ₚ(A,⌜(.newest : Term 7)⌝ₛ)⟫ }
  have sat i C : φ.denote ρ i C ↔ ∃ q A, Entry_d M i q E ∧ Entry_d M i A H ∧
      Antichain_d M B R z C ∧ (∀ r, M.mem r C → Below_d M B R z r q) ∧ M.CardinalLessOrEqual I A C := by
    simp only [φ,BinarySchema.denote,Formula.satisfies_exists_iff,Formula.satisfies_conj_iff,
      Formula.satisfies_forallMem_iff,entry_sat_l M hZFC.1,antichain_sat_l M hZFC.1,
      below_sat_l M hZFC.1,Formula.satisfies_cardinalLessOrEqual_iff I hZFC.1,Definitional.Term.eval_weaken]
    rfl
  obtain ⟨G,blocks,block⟩ := ZFC.uniformize_formula_l I hZFC φ ρ (X := ω) (Y := P) (by
    intro i hi
    obtain ⟨q,hq,iq⟩ := enumeration.1.2.2 i hi
    obtain ⟨A,_,ia⟩ := rows.2.2 i hi
    obtain ⟨μ,μκ,inf,am⟩ := ZF.small_infinite_bound_l I hZF hκ (small (decide i A ia).1) (noBig i A ia)
    have qa := below_trans_l O ha.1 (belowS q hq) hp
    obtain ⟨C,antiC,belowC,largeC⟩ := onto_antichain_unbounded_l hZF O hZFC hω inf name hb ha hT hw qa
      inf.2 (ZF.cardinal_not_le_member_l I hZF hκ.1 μκ)
    have μκ' := ZF.exists_inclusionInjection hZF I (hκ.1.1.transitive μ μκ)
    have mc := (ZF.bounded_compare_l I hZF hκ.1.1 μκ' (small antiC)).resolve_right largeC
    exact ⟨C,(power C).mpr (fun r hr => (antiC.1 r hr).1),(sat i C).mpr ⟨q,A,iq,ia,antiC,belowC,trans am mc⟩⟩)
  have block i C (ic : Entry_d M i C G) := (sat i C).mp (block i C ic)
  obtain ⟨U,range⟩ := ZF.exists_range_of_setFunction hZF I blocks.1 blocks.2.1
  obtain ⟨A,union⟩ := KP.exists_union (ZF.modelsKP hZF) U
  have member q : M.mem q A ↔ ∃ i C, Entry_d M i C G ∧ M.mem q C := by
    apply (union q).trans
    exact ⟨fun ⟨C,hC,qC⟩ => ((range C).mp hC).elim fun i ic => ⟨i,C,ic,qC⟩,
      fun ⟨i,C,ic,qC⟩ => ⟨C,(range C).mpr ⟨i,ic⟩,qC⟩⟩
  have anti : Antichain_d M B R z A := by
    refine ⟨fun q hq => ?_,fun q r hq hr compat => ?_⟩
    · obtain ⟨i,C,ic,qc⟩ := (member q).mp hq
      obtain ⟨_,_,_,_,anti,_,_⟩ := block i C ic
      exact anti.1 q qc
    · obtain ⟨i,C,ic,qc⟩ := (member q).mp hq
      obtain ⟨j,D,jd,rd⟩ := (member r).mp hr
      obtain ⟨s,_,is,_,antiC,cs,_⟩ := block i C ic
      obtain ⟨t,_,jt,_,antiD,dt,_⟩ := block j D jd
      have hs := enumeration.1.output_mem_of_pairMember is
      have ht := enumeration.1.output_mem_of_pairMember jt
      obtain ⟨v,vq,vr⟩ := compat
      have st := antiS.2 s t hs ht ⟨v,below_trans_l O (antiS.1 s hs).1 vq (cs q qc),
        O.trans v r t vq.1 (antiD.1 r rd).1 (antiS.1 t ht).1 vr (dt r rd).2.2⟩
      have ij := enumeration.2 i j s is (st.symm ▸ jt)
      subst j
      have cd := blocks.1.2 i C D ic jd
      subst D
      exact antiC.2 q r qc rd ⟨v,vq,vr⟩
  have below q (hq : M.mem q A) : Below_d M B R z q p := by
    obtain ⟨i,C,ic,qc⟩ := (member q).mp hq
    obtain ⟨s,_,is,_,_,cs,_⟩ := block i C ic
    exact below_trans_l O hp.1 (cs q qc) (belowS s (enumeration.1.output_mem_of_pairMember is))
  apply finish anti below
  apply Classical.byContradiction
  intro smallA
  obtain ⟨μ,μκ,inf,am⟩ := ZF.small_infinite_bound_l I hZF hκ (small anti) smallA
  apply ZF.cardinal_not_le_member_l I hZF hκ.1 μκ
  apply onto_antichains_bound_l hZF O hZFC hω inf name hb ha hT hw hp inf.2 rows decide
  intro i D id
  obtain ⟨C,_,ic⟩ := blocks.2.2 i (rows.input_mem_of_pairMember id)
  obtain ⟨_,D',_,id',_,_,dc⟩ := block i C ic
  have eq := rows.1.2 i D' D id' id
  subst D'
  exact trans dc (trans (ZF.exists_inclusionInjection hZF I (fun q qc => (member q).mpr ⟨i,C,ic,qc⟩)) am)

/-- 任意指定的局部稠密集都含有 κ 个元素的极大反链，而非仅仅任意大的反链。 -/
theorem collapse_dense_antichain_l {B R z a b T w f ω κ p D : M.Domain} (O : Cond_order_d M B R z)
    (hω : M.IsOmega ω) (hκ : M.IsUncountableCardinal I ω κ) (size : M.CardinalLessOrEqual I B κ)
    (name : Onto_name_d B R z a T w f) (hb : M.mem b B) (ha : Below_d M B R z a b)
    (hT : Check_d M b ω T) (hw : Check_d M b κ w) (hp : Below_d M B R z p a)
    (dense : Dense_d M B R z (fun q => M.mem q D) p) : ∃ C F,
      Antichain_d M B R z C ∧ (∀ c, M.mem c C → M.mem c D ∧ Below_d M B R z c p) ∧
      (∀ q, Below_d M B R z q p → ∃ c, M.mem c C ∧ Cmp_d M B R z q c) ∧
      M.IsSetBijectionFromTo I F κ C := by
  obtain ⟨A,J,anti,below,bij⟩ := collapse_antichain_l hZFC O hω hκ size name hb ha hT hw hp
  obtain ⟨C,G,antiC,bound,maximal,inj,_⟩ := antichain_refine_l hZFC O hp.1 dense anti below
  have lower := ZF.exists_compositionInjection hZF I bij.1 inj
  obtain ⟨K,inc⟩ := ZF.exists_inclusionInjection hZF I (fun c hc => (antiC.1 c hc).1)
  obtain ⟨L,lim⟩ := size
  have upper := ZF.exists_compositionInjection hZF I inc lim
  obtain ⟨F,bijection⟩ := ZF.equinumerous_of_cardinalLessOrEqual hZF I lower upper
  exact ⟨C,F,antiC,bound,maximal,bijection⟩

end YesMetaZFC.Model.Forcing.Internal

/-! ## Kripke 树的一步工厂

第 n 轮同时决定坍缩满射的第 n 个值，并判定是否进入该值所编号的旧条件。
这两项调度共用同一张 κ 元极大反链，后者保证最终树的稠密性。
-/
namespace YesMetaZFC.Model.Forcing.Internal
open SetTheory SetTheory.Definitional.Project
universe u
variable {M : Structure.{u}}

def Kr_decide_d (B R z b f E n c : M.Domain) : Prop := ∃ α q,
  Entry_d M α q E ∧ Old_value_d M B R z b f c n α ∧ (Entry_d M c q R ∨ ¬ Cmp_d M B R z c q)

def kr_decide_m {d} (B R z b f E n c : Term d) : Formula 1 d := set[d] ⟪∃ α, ∃ q,
  ⌜entry_m⌝ₚ(α,q,⌜E⌝ₛ) ∧ ⌜old_value_m⌝ₚ(⌜B⌝ₛ,⌜R⌝ₛ,⌜z⌝ₛ,⌜b⌝ₛ,⌜f⌝ₛ,⌜c⌝ₛ,⌜n⌝ₛ,α) ∧
    (⌜entry_m⌝ₚ(⌜c⌝ₛ,q,⌜R⌝ₛ) ∨ ¬ ⌜cmp_m⌝ₚ(⌜B⌝ₛ,⌜R⌝ₛ,⌜z⌝ₛ,⌜c⌝ₛ,q))⟫
derive_free_closed kr_decide_m

theorem kr_decide_sat_l (hE : Extensional M) {d} (ρ : Env M d) (B R z b f E n c : Term d) :
    Formula.satisfies ρ (kr_decide_m B R z b f E n c) ↔
      Kr_decide_d (B.eval ρ) (R.eval ρ) (z.eval ρ) (b.eval ρ) (f.eval ρ) (E.eval ρ) (n.eval ρ) (c.eval ρ) := by
  simp only [kr_decide_m,Kr_decide_d,Formula.satisfies_exists_iff,Formula.satisfies_conj_iff,
    Formula.satisfies_disj_iff,Formula.satisfies_neg_iff,entry_sat_l M hE,old_value_sat_l hE,
    cmp_sat_l M hE,Definitional.Term.eval_weaken]
  rfl

variable (hZFC : M.Models ZFC) {B R z a b T w f ω κ E : M.Domain} (O : Cond_order_d M B R z)
local notation "hZF" => ZFC.models_zf_l hZFC
local notation "I" => kpair_interpretation_l M (And.left hZFC) (KP.exists_pair (ZF.modelsKP hZF))
include O

theorem kr_step_l (hω : M.IsOmega ω) (hκ : M.IsUncountableCardinal I ω κ) (size : M.CardinalLessOrEqual I B κ)
    (name : Onto_name_d B R z a T w f) (hb : M.mem b B) (ha : Below_d M B R z a b)
    (hT : Check_d M b ω T) (hw : Check_d M b κ w) (enum : M.IsSetFunctionFromTo I E κ B)
    {p n : M.Domain} (hp : Below_d M B R z p a) (hn : M.mem n ω) : ∃ A F,
      Antichain_d M B R z A ∧ (∀ c, M.mem c A → Below_d M B R z c p ∧ Kr_decide_d B R z b f E n c) ∧
      (∀ q, Below_d M B R z q p → ∃ c, M.mem c A ∧ Cmp_d M B R z q c) ∧ M.IsSetBijectionFromTo I F κ A := by
  classical
  let ρ : Env M 7 := ⟨fun i => [B,R,z,b,f,E,n].get i,fun _ => p⟩
  let φ : UnarySchema 7 := {
    body := kr_decide_m (.bound 1) (.bound 2) (.bound 3) (.bound 4) (.bound 5) (.bound 6) (.bound 7) .newest }
  obtain ⟨D,members⟩ := ZF.separation_exists_d hZF φ ρ B
  have member c : M.mem c D ↔ M.mem c B ∧ Kr_decide_d B R z b f E n c :=
    (members c).trans (and_congr_right fun _ => kr_decide_sat_l hZFC.1 ..)
  have dense : Dense_d M B R z (fun c => M.mem c D) p := by
    intro q hq
    obtain ⟨r,hr,α,hα,value⟩ := old_value_dense_l O hZF name.1 hb ha hT hw hn q (below_trans_l O ha.1 hq hp)
    obtain ⟨s,hs,αs⟩ := enum.2.2 α hα
    by_cases compat : Cmp_d M B R z r s
    · obtain ⟨t,ht,ts⟩ := compat
      exact ⟨t,below_trans_l O hq.1 ht hr,(member t).mpr ⟨ht.1,α,s,αs,
        old_value_lower_l O hZF hb name.1.2.2.1 r t hr.1 ht value,Or.inl ts⟩⟩
    · exact ⟨r,hr,(member r).mpr ⟨hr.1,α,s,αs,value,Or.inr compat⟩⟩
  obtain ⟨A,F,anti,bound,maximal,bij⟩ := collapse_dense_antichain_l hZFC O hω hκ size name hb ha hT hw hp dense
  exact ⟨A,F,anti,(fun c hc => ⟨(bound c hc).2,((member c).mp (bound c hc).1).2⟩),maximal,bij⟩

end YesMetaZFC.Model.Forcing.Internal

/-! ## 全部内部回合与正条件的 κ 叉工厂

一步编号表属于 κ×B 的内部幂集。对 ω×(B↾a) 统一选择这些表，得到
后续内部历史递归所需的单一集合函数。
-/
namespace YesMetaZFC.Model.Forcing.Internal
open SetTheory SetTheory.Definitional.Project
universe u
variable {M : Structure.{u}} (hZF : M.Models ZF)
local notation "I" => kpair_interpretation_l M (And.left hZF) (KP.exists_pair (ZF.modelsKP hZF))

structure Kr_branch_d (B R z b f E κ n p F : M.Domain) : Prop where
  function : M.IsSetFunctionFromTo I F κ B
  below : ∀ α q, Entry_d M α q F → Below_d M B R z q p ∧ Kr_decide_d B R z b f E n q
  separate : ∀ α β q r, Entry_d M α q F → Entry_d M β r F → Cmp_d M B R z q r → α = β
  maximal : ∀ r, Below_d M B R z r p → ∃ α q, Entry_d M α q F ∧ Cmp_d M B R z r q

def kr_branch_m {d} (B R z b f E κ n p F : Term d) : Formula 1 d := set[d] ⟪
  ⌜(Formula.isFunctionFromTo kpair_convention_l)⌝ₚ(⌜F⌝ₛ,⌜κ⌝ₛ,⌜B⌝ₛ) ∧
  (∀ α q, ⌜entry_m⌝ₚ(α,q,⌜F⌝ₛ) → ⌜below_m⌝ₚ(⌜B⌝ₛ,⌜R⌝ₛ,⌜z⌝ₛ,q,⌜p⌝ₛ) ∧
    ⌜kr_decide_m⌝ₚ(⌜B⌝ₛ,⌜R⌝ₛ,⌜z⌝ₛ,⌜b⌝ₛ,⌜f⌝ₛ,⌜E⌝ₛ,⌜n⌝ₛ,q)) ∧
  (∀ α β q r, ⌜entry_m⌝ₚ(α,q,⌜F⌝ₛ) → ⌜entry_m⌝ₚ(β,r,⌜F⌝ₛ) → ⌜cmp_m⌝ₚ(⌜B⌝ₛ,⌜R⌝ₛ,⌜z⌝ₛ,q,r) → α = β) ∧
  (∀ r, ⌜below_m⌝ₚ(⌜B⌝ₛ,⌜R⌝ₛ,⌜z⌝ₛ,r,⌜p⌝ₛ) → ∃ α q, ⌜entry_m⌝ₚ(α,q,⌜F⌝ₛ) ∧ ⌜cmp_m⌝ₚ(⌜B⌝ₛ,⌜R⌝ₛ,⌜z⌝ₛ,r,q))⟫
derive_free_closed kr_branch_m

theorem kr_branch_sat_l {d} (ρ : Env M d) (B R z b f E κ n p F : Term d) :
    Formula.satisfies ρ (kr_branch_m B R z b f E κ n p F) ↔
      Kr_branch_d hZF (B.eval ρ) (R.eval ρ) (z.eval ρ) (b.eval ρ) (f.eval ρ) (E.eval ρ)
        (κ.eval ρ) (n.eval ρ) (p.eval ρ) (F.eval ρ) := by
  simp only [kr_branch_m,Formula.satisfies_conj_iff,Formula.satisfies_forall_iff,
    Formula.satisfies_exists_iff,Formula.satisfies_imp_iff,entry_sat_l M hZF.1,below_sat_l M hZF.1,
    cmp_sat_l M hZF.1,kr_decide_sat_l hZF.1,Formula.satisfies_extensionalEq_iff_eq hZF.1,
    Formula.satisfies_isFunctionFromTo_iff I hZF.1,Definitional.Term.eval_weaken]
  exact ⟨fun h => ⟨h.1,h.2.1,h.2.2.1,h.2.2.2⟩,fun h => ⟨h.function,h.below,h.separate,h.maximal⟩⟩

theorem kr_factory_l (hZFC : M.Models ZFC) {B R z a b T w f ω κ E : M.Domain} (O : Cond_order_d M B R z)
    (hω : M.IsOmega ω) (hκ : M.IsUncountableCardinal I ω κ) (size : M.CardinalLessOrEqual I B κ)
    (name : Onto_name_d B R z a T w f) (hb : M.mem b B) (ha : Below_d M B R z a b)
    (hT : Check_d M b ω T) (hw : Check_d M b κ w) (enum : M.IsSetFunctionFromTo I E κ B) :
    ∃ C S P H, (∀ p, M.mem p C ↔ Below_d M B R z p a) ∧ M.IsCartesianProduct I S ω C ∧
      M.IsSetFunctionFromTo I H S P ∧ ∀ s F n p, Entry_d M s F H → (I).Codes s n p →
        Kr_branch_d hZF B R z b f E κ n p F := by
  let ρ₀ : Env M 4 := ⟨fun i => [B,R,z,a].get i,fun _ => a⟩
  let ψ : UnarySchema 4 := { body := below_m (.bound 1) (.bound 2) (.bound 3) .newest (.bound 4) }
  obtain ⟨C,members⟩ := ZF.separation_exists_d hZF ψ ρ₀ B
  have cone p : M.mem p C ↔ Below_d M B R z p a :=
    ((members p).trans (and_congr_right fun _ => below_sat_l M hZF.1 ..)).trans ⟨And.right,fun h => ⟨h.1,h⟩⟩
  obtain ⟨S,states⟩ := ZF.exists_cartesianProduct hZF I ω C
  obtain ⟨W,product⟩ := ZF.exists_cartesianProduct hZF I κ B
  obtain ⟨P,power⟩ := ZF.exists_powerSet hZF W
  let ρ : Env M 7 := ⟨fun i => [B,R,z,b,f,E,κ].get i,fun _ => b⟩
  let φ : BinarySchema 7 := { body := set[9] ⟪∃ n p,
    ⌜kpair_m⌝ₚ(⌜(.bound 1 : Term 9)⌝ₛ,n,p) ∧
    ⌜kr_branch_m⌝ₚ(⌜(.bound 2 : Term 9)⌝ₛ,⌜(.bound 3 : Term 9)⌝ₛ,⌜(.bound 4 : Term 9)⌝ₛ,⌜(.bound 5 : Term 9)⌝ₛ,
      ⌜(.bound 6 : Term 9)⌝ₛ,⌜(.bound 7 : Term 9)⌝ₛ,⌜(.bound 8 : Term 9)⌝ₛ,n,p,⌜(.newest : Term 9)⌝ₛ)⟫ }
  have sat s F : φ.denote ρ s F ↔ ∃ n p, (I).Codes s n p ∧ Kr_branch_d hZF B R z b f E κ n p F := by
    simp only [φ,BinarySchema.denote,Formula.satisfies_exists_iff,Formula.satisfies_conj_iff,
      kpair_sat_l M hZF.1,kr_branch_sat_l hZF,Definitional.Term.eval_weaken]
    rfl
  obtain ⟨H,fn,values⟩ := ZFC.uniformize_formula_l I hZFC φ ρ (X := S) (Y := P) (by
    intro s hs
    obtain ⟨n,hn,p,hp,pair⟩ := (states s).mp hs
    obtain ⟨A,F,anti,bound,maximal,bij⟩ := kr_step_l hZFC O hω hκ size name hb ha hT hw enum ((cone p).mp hp) hn
    have typed : M.IsSetFunctionFromTo I F κ B := ⟨bij.1.1.1,bij.1.1.2.1,fun α hα => by
      obtain ⟨q,hq,αq⟩ := bij.1.1.2.2 α hα
      exact ⟨q,(anti.1 q hq).1,αq⟩⟩
    refine ⟨F,(power F).mpr ?_,(sat s F).mpr ⟨n,p,pair,typed,?_,?_,?_⟩⟩
    · intro v hv
      obtain ⟨α,q,pair⟩ := typed.1.1 v hv
      have edge : Entry_d M α q F := ⟨v,pair,hv⟩
      exact (product v).mpr ⟨α,typed.input_mem_of_pairMember edge,q,typed.output_mem_of_pairMember edge,pair⟩
    · intro α q αq
      exact bound q (bij.1.1.output_mem_of_pairMember αq)
    · intro α β q r αq βr compat
      have eq := anti.2 q r (bij.1.1.output_mem_of_pairMember αq) (bij.1.1.output_mem_of_pairMember βr) compat
      exact bij.1.2 α β q αq (eq.symm ▸ βr)
    · intro r hr
      obtain ⟨q,hq,rq⟩ := maximal r hr
      obtain ⟨α,_,αq⟩ := bij.2 q hq
      exact ⟨α,q,αq,rq⟩)
  refine ⟨C,S,P,H,cone,states,fn,fun s F n p sf pair => ?_⟩
  obtain ⟨m,q,pair',branch⟩ := (sat s F).mp (values s F sf)
  obtain ⟨rfl,rfl⟩ := (I).injective pair pair'
  exact branch

end YesMetaZFC.Model.Forcing.Internal

/-! ## κ 叉工厂的确定状态转移

状态为内部回合号与当前条件的有序对。转移读取工厂编号表中的指定分支，
整个有限历史求值复用既有内部历史递归。
-/
namespace YesMetaZFC.Model.Forcing.Internal
open SetTheory SetTheory.Definitional.Project
universe u
variable {M : Structure.{u}}

def Kr_next_d (H s α t : M.Domain) : Prop := ∃ n p m F q,
  KPair_d M s n p ∧ M.SuccessorOf m n ∧ Entry_d M s F H ∧ Entry_d M α q F ∧ KPair_d M t m q

def kr_next_m {d} (H s α t : Term d) : Formula 1 d := set[d] ⟪∃ n p m F q,
  ⌜kpair_m⌝ₚ(⌜s⌝ₛ,n,p) ∧ ⌜Formula.isSuccessor⌝ₚ(m,n) ∧
  ⌜entry_m⌝ₚ(⌜s⌝ₛ,F,⌜H⌝ₛ) ∧ ⌜entry_m⌝ₚ(⌜α⌝ₛ,q,F) ∧ ⌜kpair_m⌝ₚ(⌜t⌝ₛ,m,q)⟫
derive_free_closed kr_next_m

theorem kr_next_sat_l (hE : Extensional M) {d} (ρ : Env M d) (H s α t : Term d) :
    Formula.satisfies ρ (kr_next_m H s α t) ↔ Kr_next_d (H.eval ρ) (s.eval ρ) (α.eval ρ) (t.eval ρ) := by
  simp only [kr_next_m,Kr_next_d,Formula.satisfies_exists_iff,Formula.satisfies_conj_iff,
    kpair_sat_l M hE,Formula.satisfies_isSuccessor_iff,entry_sat_l M hE,Definitional.Term.eval_weaken]
  rfl

variable (hZF : M.Models ZF) {B R z a b f E ω κ C S P H : M.Domain}
local notation "I" => kpair_interpretation_l M (And.left hZF) (KP.exists_pair (ZF.modelsKP hZF))

theorem kr_machine_l (O : Cond_order_d M B R z) (hω : M.IsOmega ω) (ha : M.mem a B)
    (cone : ∀ p, M.mem p C ↔ Below_d M B R z p a) (states : M.IsCartesianProduct I S ω C)
    (factory : M.IsSetFunctionFromTo I H S P)
    (branches : ∀ s F n p, Entry_d M s F H → (I).Codes s n p → Kr_branch_d hZF B R z b f E κ n p F) :
    ∃ D K, M.IsCartesianProduct I D S κ ∧ M.IsSetFunctionFromTo I K D S ∧
      ∀ v t, Entry_d M v t K ↔ M.mem v D ∧ ∃ s α, (I).Codes v s α ∧ Kr_next_d H s α t := by
  obtain ⟨D,inputs⟩ := ZF.exists_cartesianProduct hZF I S κ
  let ρ : Env M 1 := ⟨fun _ => H,fun _ => H⟩
  let φ : BinarySchema 1 := { body := set[3] ⟪∃ s α,
    ⌜kpair_m⌝ₚ(⌜(.bound 1 : Term 3)⌝ₛ,s,α) ∧ ⌜kr_next_m⌝ₚ(⌜(.bound 2 : Term 3)⌝ₛ,s,α,⌜(.newest : Term 3)⌝ₛ)⟫ }
  have sat v t : φ.denote ρ v t ↔ ∃ s α, (I).Codes v s α ∧ Kr_next_d H s α t := by
    simp only [φ,BinarySchema.denote,Formula.satisfies_exists_iff,Formula.satisfies_conj_iff,
      kpair_sat_l M hZF.1,kr_next_sat_l hZF.1,Definitional.Term.eval_weaken]
    rfl
  have typed {s α t} (hs : M.mem s S) (step : Kr_next_d H s α t) : M.mem t S := by
    obtain ⟨n,p,m,F,q,pair,succ,sF,αq,out⟩ := step
    obtain ⟨n',hn,p',hp,pair'⟩ := (states s).mp hs
    obtain ⟨rfl,rfl⟩ := (I).injective pair pair'
    obtain ⟨m',succ',hm⟩ := hω.1.2 n hn
    have hm : M.mem m ω := succ'.eq hZF.1 succ ▸ hm
    have qa := below_trans_l O ha ((branches s F n p sF pair).below α q αq).1 ((cone p).mp hp)
    exact (states t).mpr ⟨m,hm,q,(cone q).mpr qa,out⟩
  obtain ⟨K,fn,values⟩ := ZF.exists_setFunctionFromTo_of_denote hZF I φ ρ (source := D) (target := S) (by
    intro v hv
    obtain ⟨s,hs,α,hα,input⟩ := (inputs v).mp hv
    obtain ⟨n,hn,p,_,pair⟩ := (states s).mp hs
    obtain ⟨F,_,sF⟩ := factory.2.2 s hs
    obtain ⟨q,_,αq⟩ := (branches s F n p sF pair).function.2.2 α hα
    obtain ⟨m,succ,_⟩ := hω.1.2 n hn
    obtain ⟨t,out⟩ := (I).total m q
    exact ⟨t,(sat v t).mpr ⟨s,α,input,n,p,m,F,q,pair,succ,sF,αq,out⟩⟩) (by
    intro v _ t u ht hu
    obtain ⟨s,α,input,n,p,m,F,q,pair,succ,sF,αq,out⟩ := (sat v t).mp ht
    obtain ⟨s',α',input',n',p',m',F',q',pair',succ',sF',αq',out'⟩ := (sat v u).mp hu
    obtain ⟨rfl,rfl⟩ := (I).injective input input'
    obtain ⟨rfl,rfl⟩ := (I).injective pair pair'
    have mm := succ.eq hZF.1 succ'
    subst m'
    have ff := factory.1.2 s F F' sF sF'
    subst F'
    have qq := (branches s F n p sF pair).function.1.2 α q q' αq αq'
    subst q'
    exact (I).unique out out') (by
    intro v t hv ht
    obtain ⟨s,α,input,step⟩ := (sat v t).mp ht
    obtain ⟨s',hs,α',_,input'⟩ := (inputs v).mp hv
    obtain ⟨rfl,rfl⟩ := (I).injective input input'
    exact typed hs step)
  exact ⟨D,K,inputs,fn,fun v t => (values v t).trans (and_congr_right fun _ => sat v t)⟩

/-- 由一个实际工厂直接收集全部内部有限历史的状态求值表。 -/
theorem kr_history_l (O : Cond_order_d M B R z) (hω : M.IsOmega ω) (ha : M.mem a B) (hz : a ≠ z)
    (hk : ∃ α, M.mem α κ) (cone : ∀ p, M.mem p C ↔ Below_d M B R z p a)
    (states : M.IsCartesianProduct I S ω C) (factory : M.IsSetFunctionFromTo I H S P)
    (branches : ∀ s F n p, Entry_d M s F H → (I).Codes s n p → Kr_branch_d hZF B R z b f E κ n p F) :
    ∃ D K F o r π, M.IsCartesianProduct I D S κ ∧ M.IsSetFunctionFromTo I K D S ∧
      (∀ v t, Entry_d M v t K ↔ M.mem v D ∧ ∃ s α, (I).Codes v s α ∧ Kr_next_d H s α t) ∧
      Fseq_space_d I ω κ F ∧ (∀ x, ¬ M.mem x o) ∧ (I).Codes r o a ∧
      M.IsSetFunctionFromTo I π F S ∧ ∀ s t, Entry_d M s t π ↔ M.mem s F ∧
        Descriptive.Hr_eval_d hZF ω κ S K r s t := by
  obtain ⟨D,K,inputs,next,values⟩ := kr_machine_l hZF O hω ha cone states factory branches
  obtain ⟨F,space⟩ := ZF.fseq_space_exists_l I hZF hω κ
  obtain ⟨o,empty,ho⟩ := hω.1.1
  obtain ⟨r,pair⟩ := (I).total o a
  obtain ⟨α,hα⟩ := hk
  obtain ⟨π,fn,graph⟩ := Descriptive.hr_eval_table_l hZF hω space inputs
    (InnerModel.fn0_of_function_l (ZF.modelsKP hZF) next)
    ((states r).mpr ⟨o,ho,a,(cone a).mpr (below_refl_l O ha hz),pair⟩) hα
  exact ⟨D,K,F,o,r,π,inputs,next,values,space,empty,pair,
    InnerModel.fn0_function_l (ZF.modelsKP hZF) fn,graph⟩

end YesMetaZFC.Model.Forcing.Internal

/-! ## 内部运行的回合坐标不变量 -/
namespace YesMetaZFC.Model.Forcing.Internal
open SetTheory SetTheory.Definitional.Project SetTheory.InnerModel SetTheory.Descriptive
universe u
variable {M : Structure.{u}} (hZF : M.Models ZF)
local notation "I" => kpair_interpretation_l M (And.left hZF) (KP.exists_pair (ZF.modelsKP hZF))

theorem kr_run_index_l {ω S H D K o r f G : M.Domain} (hω : M.IsOmega ω)
    (empty : ∀ x, ¬ M.mem x o) {a : M.Domain} (initial : (I).Codes r o a)
    (edges : ∀ v t, Entry_d M v t K ↔ M.mem v D ∧ ∃ s α, (I).Codes v s α ∧ Kr_next_d H s α t)
    (run : Hr_run_d hZF ω S K r f G) : ∀ n, M.mem n ω → ∀ t, Entry_d M n t G → ∃ q, (I).Codes t n q := by
  let ρ : Env M 1 := ⟨fun _ => G,fun _ => G⟩
  let φ : UnarySchema 1 := { body := set[2] ⟪∀ t,
    ⌜entry_m⌝ₚ(⌜(.newest : Term 2)⌝ₛ,t,⌜(.bound 1 : Term 2)⌝ₛ) →
      ∃ q, ⌜kpair_m⌝ₚ(t,⌜(.newest : Term 2)⌝ₛ,q)⟫ }
  have sat n : φ.denote ρ n ↔ ∀ t, Entry_d M n t G → ∃ q, (I).Codes t n q := by
    simp only [φ,UnarySchema.denote,Formula.satisfies_forall_iff,Formula.satisfies_imp_iff,
      Formula.satisfies_exists_iff,entry_sat_l M hZF.1,kpair_sat_l M hZF.1,Definitional.Term.eval_weaken]
    rfl
  apply hω.induction
  · obtain ⟨A,member⟩ := ZF.separation_exists_d hZF φ ρ ω
    exact ⟨A,fun n => (member n).trans (and_congr_right fun _ => sat n)⟩
  · intro e he t et
    have eo := hZF.1.eq_of_same_members e o (fun x => iff_of_false (he x) (empty x))
    have tr := (fn0_function_l (ZF.modelsKP hZF) run.1).1.2 e t r et (run.2.1 e he)
    exact ⟨a,tr.symm ▸ eo.symm ▸ initial⟩
  · intro n hn ih m succ t mt
    obtain ⟨s,_,ns⟩ := run.1.2.1 n hn
    obtain ⟨p,pair⟩ := ih s ns
    obtain ⟨α,v,_,input,vt⟩ := run.2.2 n m s t succ ns mt
    obtain ⟨_,s',α',input',i,q,j,F,u,pair',next,_,_,output⟩ := (edges v t).mp vt
    obtain ⟨rfl,rfl⟩ := (I).injective input input'
    obtain ⟨rfl,rfl⟩ := (I).injective pair pair'
    exact ⟨u,(next.eq hZF.1 succ) ▸ output⟩

theorem Hr_eval_d.kr_index_l {ω κ S H D K o r s t a : M.Domain} (hω : M.IsOmega ω)
    (empty : ∀ x, ¬ M.mem x o) (initial : (I).Codes r o a)
    (edges : ∀ v t, Entry_d M v t K ↔ M.mem v D ∧ ∃ s α, (I).Codes v s α ∧ Kr_next_d H s α t)
    (eval : Hr_eval_d hZF ω κ S K r s t) : ∃ n q, M.mem n ω ∧ M.IsDomainOf I n s ∧ (I).Codes t n q := by
  obtain ⟨n,f,G,hn,fn,cut,run,nt⟩ := eval
  obtain ⟨q,pair⟩ := kr_run_index_l hZF hω empty initial edges run n hn t nt
  exact ⟨n,q,hn,(cut.isSetFunctionFromTo (fn0_function_l (ZF.modelsKP hZF) fn)
    (hω.transitive (ZF.modelsKP hZF) n hn)).2.1,pair⟩

end YesMetaZFC.Model.Forcing.Internal

/-! ## Kripke 构造的实际内部 κ 叉树

投影有限历史求值表的条件坐标。每个节点的全部直接后继精确等于工厂中的
κ 元极大反链，同时保留该层的原满射判值与旧条件调度。
-/
namespace YesMetaZFC.Model.Forcing.Internal
open SetTheory SetTheory.Definitional.Project SetTheory.Descriptive
universe u
variable {M : Structure.{u}} (hZF : M.Models ZF)
local notation "I" => kpair_interpretation_l M (And.left hZF) (KP.exists_pair (ZF.modelsKP hZF))

structure Kr_tree_d (B R z a b f E ω κ F Γ : M.Domain) : Prop where
  space : Fseq_space_d I ω κ F
  function : M.IsSetFunctionFromTo I Γ F B
  below : ∀ s q, Entry_d M s q Γ → Below_d M B R z q a
  root : ∀ e, (∀ x, ¬ M.mem x e) → Entry_d M e a Γ
  children : ∀ s q n, Entry_d M s q Γ → M.IsSetFunctionFromTo I s n κ → ∃ J,
    Kr_branch_d hZF B R z b f E κ n q J ∧ ∀ t α r, M.mem t F → Fseq_end_d I ω t s α →
      (Entry_d M t r Γ ↔ Entry_d M α r J)

theorem kr_tree_l (hZFC : M.Models ZFC) {B R z a b T w f ω κ E : M.Domain} (O : Cond_order_d M B R z)
    (hω : M.IsOmega ω) (hκ : M.IsUncountableCardinal I ω κ) (size : M.CardinalLessOrEqual I B κ)
    (name : Onto_name_d B R z a T w f) (hb : M.mem b B) (ha : Below_d M B R z a b)
    (hT : Check_d M b ω T) (hw : Check_d M b κ w) (enum : M.IsSetFunctionFromTo I E κ B) :
    ∃ F Γ, Kr_tree_d hZF B R z a b f E ω κ F Γ := by
  obtain ⟨C,S,P,H,cone,states,factory,branches⟩ := kr_factory_l hZF hZFC O hω hκ size name hb ha hT hw enum
  obtain ⟨D,K,F,o,r,π,inputs,next,edges,space,empty,initial,fn,values⟩ :=
    kr_history_l hZF O hω ha.1 ha.2.1 ⟨ω,hκ.2⟩ cone states factory branches
  let ρ : Env M 1 := ⟨fun _ => π,fun _ => π⟩
  let φ : BinarySchema 1 := { body := set[3] ⟪∃ t n,
    ⌜entry_m⌝ₚ(⌜(.bound 1 : Term 3)⌝ₛ,t,⌜(.bound 2 : Term 3)⌝ₛ) ∧
      ⌜kpair_m⌝ₚ(t,n,⌜(.newest : Term 3)⌝ₛ)⟫ }
  have sat s q : φ.denote ρ s q ↔ ∃ t n, Entry_d M s t π ∧ (I).Codes t n q := by
    simp only [φ,BinarySchema.denote,Formula.satisfies_exists_iff,Formula.satisfies_conj_iff,
      entry_sat_l M hZF.1,kpair_sat_l M hZF.1,Definitional.Term.eval_weaken]
    rfl
  have bound {s t n q} (st : Entry_d M s t π) (pair : (I).Codes t n q) : M.mem q C := by
    obtain ⟨n',_,q',hq,pair'⟩ := (states t).mp (fn.output_mem_of_pairMember st)
    obtain ⟨rfl,rfl⟩ := (I).injective pair pair'
    exact hq
  obtain ⟨Γ,map,graph⟩ := ZF.exists_setFunctionFromTo_of_denote hZF I φ ρ (source := F) (target := B) (by
    intro s hs
    obtain ⟨t,ht,st⟩ := fn.2.2 s hs
    obtain ⟨n,_,q,_,pair⟩ := (states t).mp ht
    exact ⟨q,(sat s q).mpr ⟨t,n,st,pair⟩⟩) (by
    intro s _ p q hp hq
    obtain ⟨t,n,st,pair⟩ := (sat s p).mp hp
    obtain ⟨u,m,su,pair'⟩ := (sat s q).mp hq
    have eq := fn.1.2 s t u st su
    exact ((I).injective pair (eq.symm ▸ pair')).2) (by
    intro s q _ hq
    obtain ⟨t,n,st,pair⟩ := (sat s q).mp hq
    exact ((cone q).mp (bound st pair)).1)
  have graph s q : Entry_d M s q Γ ↔ M.mem s F ∧ ∃ t n, Entry_d M s t π ∧ (I).Codes t n q :=
    (graph s q).trans (and_congr_right fun _ => sat s q)
  refine ⟨F,Γ,space,map,?_,?_,?_⟩
  · intro s q sq
    obtain ⟨_,t,n,st,pair⟩ := (graph s q).mp sq
    exact (cone q).mp (bound st pair)
  · intro e he
    obtain ⟨o',empty',ho'⟩ := hω.1.1
    have heω := hZF.1.eq_of_same_members e o' (fun x => iff_of_false (he x) (empty' x))
    have heF := (space e).mpr ⟨e,heω.symm ▸ ho',ds_empty_fun_l I he⟩
    obtain ⟨t,_,et⟩ := fn.2.2 e heF
    have tr := (((values e t).mp et).2).zero_l hZF hω he
    exact (graph e a).mpr ⟨heF,r,o,tr ▸ et,initial⟩
  · intro s q n sq sn
    obtain ⟨_,v,m,sv,pair⟩ := (graph s q).mp sq
    have evalS := ((values s v).mp sv).2
    obtain ⟨m',q',_,domain,pair'⟩ := Hr_eval_d.kr_index_l hZF hω empty initial edges evalS
    obtain ⟨rfl,rfl⟩ := (I).injective pair pair'
    have mn := domain.eq hZF.1 sn.2.1
    subst m
    obtain ⟨J,_,vJ⟩ := factory.2.2 v (fn.output_mem_of_pairMember sv)
    have branch := branches v J n q vJ pair
    have forward t α u (ht : M.mem t F) (end' : Fseq_end_d I ω t s α) (tu : Entry_d M t u Γ) : Entry_d M α u J := by
      obtain ⟨_,v',m',tv',out⟩ := (graph t u).mp tu
      have evalT := ((values t v').mp tv').2
      obtain ⟨v₀,input,step⟩ := evalS.step_l hZF hω next.1 evalT end'
      obtain ⟨_,v'',α',input',i,p,j,J',u',pair',succ,vJ',αu,out'⟩ := (edges v₀ v').mp step
      obtain ⟨rfl,rfl⟩ := (I).injective input input'
      obtain ⟨rfl,rfl⟩ := (I).injective pair pair'
      have jj := factory.1.2 v J' J vJ' vJ
      have uu := ((I).injective out' out).2
      exact jj ▸ uu ▸ αu
    refine ⟨J,branch,fun t α u ht end' => ⟨forward t α u ht end',fun αu => ?_⟩⟩
    obtain ⟨u',_,tu⟩ := map.2.2 t ht
    have eq := branch.function.1.2 α u' u (forward t α u' ht end' tu) αu
    exact eq ▸ tu

end YesMetaZFC.Model.Forcing.Internal

/-! ## 内部 κ 叉树的层预稠密性与全树稠密性

层数由模型内部 ω 归纳。全树稠密性利用同一满射名字找到旧条件的编号，
再用对应轮次的判值与进入／排除二择，得到真正位于该条件以下的节点。
-/
namespace YesMetaZFC.Model.Forcing.Internal
open SetTheory SetTheory.Definitional.Project SetTheory.Descriptive
universe u
variable {M : Structure.{u}} (hZF : M.Models ZF)
local notation "I" => kpair_interpretation_l M (And.left hZF) (KP.exists_pair (ZF.modelsKP hZF))
variable {B R z a b f E ω κ F Γ : M.Domain} (O : Cond_order_d M B R z) (hω : M.IsOmega ω)
include O hω

theorem Kr_tree_d.level_l (tree : Kr_tree_d hZF B R z a b f E ω κ F Γ) :
    ∀ n, M.mem n ω → ∀ q, Below_d M B R z q a → ∃ s c,
      M.IsSetFunctionFromTo I s n κ ∧ Entry_d M s c Γ ∧ Cmp_d M B R z q c := by
  let ρ : Env M 6 := ⟨fun i => [B,R,z,a,κ,Γ].get i,fun _ => a⟩
  let φ : UnarySchema 6 := { body := set[7] ⟪∀ q,
    ⌜below_m⌝ₚ(⌜(.bound 1 : Term 7)⌝ₛ,⌜(.bound 2 : Term 7)⌝ₛ,⌜(.bound 3 : Term 7)⌝ₛ,q,⌜(.bound 4 : Term 7)⌝ₛ) → ∃ s c,
    ⌜(Formula.isFunctionFromTo kpair_convention_l)⌝ₚ(s,⌜(.newest : Term 7)⌝ₛ,⌜(.bound 5 : Term 7)⌝ₛ) ∧
    ⌜entry_m⌝ₚ(s,c,⌜(.bound 6 : Term 7)⌝ₛ) ∧ ⌜cmp_m⌝ₚ(⌜(.bound 1 : Term 7)⌝ₛ,⌜(.bound 2 : Term 7)⌝ₛ,⌜(.bound 3 : Term 7)⌝ₛ,q,c)⟫ }
  have sat n : φ.denote ρ n ↔ ∀ q, Below_d M B R z q a → ∃ s c,
      M.IsSetFunctionFromTo I s n κ ∧ Entry_d M s c Γ ∧ Cmp_d M B R z q c := by
    simp only [φ,UnarySchema.denote,Formula.satisfies_forall_iff,Formula.satisfies_imp_iff,
      Formula.satisfies_exists_iff,Formula.satisfies_conj_iff,below_sat_l M hZF.1,entry_sat_l M hZF.1,
      cmp_sat_l M hZF.1,Formula.satisfies_isFunctionFromTo_iff I hZF.1,Definitional.Term.eval_weaken]
    rfl
  apply hω.induction
  · obtain ⟨A,member⟩ := ZF.separation_exists_d hZF φ ρ ω
    exact ⟨A,fun n => (member n).trans (and_congr_right fun _ => sat n)⟩
  · intro e empty q hq
    exact ⟨e,a,ds_empty_fun_l I empty,tree.root e empty,q,below_refl_l O hq.1 hq.2.1,hq.2.2⟩
  · intro n hn ih m succ q hq
    obtain ⟨s,c,sn,sc,u,uq,uc⟩ := ih q hq
    obtain ⟨J,branch,children⟩ := tree.children s c n sc sn
    obtain ⟨α,d,αd,v,vu,vd⟩ := branch.maximal u ⟨uq.1,uq.2.1,uc⟩
    obtain ⟨m',t,hm,tm,end'⟩ := ZF.fseq_end_exists_l I hZF hω hn sn (branch.function.input_mem_of_pairMember αd)
    have mm : m' = m := by
      obtain ⟨k,l,decomp⟩ := end'
      have eq := decomp.source.2.2.2.eq hZF.1 tm.2.1
      subst k
      have eq := decomp.prefix_sequence.2.2.2.eq hZF.1 sn.2.1
      subst l
      exact decomp.length_successor.eq hZF.1 succ
    exact ⟨t,d,mm ▸ tm,(children t α d ((tree.space t).mpr ⟨m',hm,tm⟩) end').mpr αd,
      v,below_trans_l O hq.1 vu uq,vd⟩

omit O in
theorem Kr_tree_d.decision_l (tree : Kr_tree_d hZF B R z a b f E ω κ F Γ)
    {s c n m : M.Domain} (sc : Entry_d M s c Γ) (sn : M.IsSetFunctionFromTo I s m κ)
    (hn : M.mem n ω) (succ : M.SuccessorOf m n) : Kr_decide_d B R z b f E n c := by
  obtain ⟨m',hm,sm⟩ := (tree.space s).mp (tree.function.input_mem_of_pairMember sc)
  have eq := sm.2.1.eq hZF.1 sn.2.1
  subst m'
  obtain ⟨t,cut⟩ := ZF.exists_restriction hZF I s n
  have tn := cut.isSetFunctionFromTo sn (fun i hi => (succ i).mpr (Or.inl hi))
  obtain ⟨α,hα,nα⟩ := sn.2.2 n succ.predecessor_mem
  have end' : Fseq_end_d I ω s t α := ⟨m,n,⟨hm,hω.members_areOrdinals (ZF.modelsKP hZF) m hm,sn.1,sn.2.1⟩,
    hn,succ,⟨hn,hω.members_areOrdinals (ZF.modelsKP hZF) n hn,tn.1,tn.2.1⟩,cut,nα⟩
  obtain ⟨q,_,tq⟩ := tree.function.2.2 t ((tree.space t).mpr ⟨n,hn,tn⟩)
  obtain ⟨J,branch,children⟩ := tree.children t q n tq tn
  exact (branch.below α c ((children s α c (tree.function.input_mem_of_pairMember sc) end').mp sc)).2

theorem Kr_tree_d.dense_l (tree : Kr_tree_d hZF B R z a b f E ω κ F Γ)
    {T w : M.Domain} (name : Onto_name_d B R z a T w f) (hb : M.mem b B) (ha : Below_d M B R z a b)
    (hT : Check_d M b ω T) (hw : Check_d M b κ w)
    (enum : M.IsSetFunctionFromTo I E κ B) (onto : M.IsSetSurjectiveOnto I E κ B) :
    ∀ q, Below_d M B R z q a → ∃ s c, Entry_d M s c Γ ∧ Below_d M B R z c q := by
  intro q hq
  obtain ⟨α,hα,αq⟩ := onto q hq.1
  obtain ⟨r,hr,n,hn,value⟩ := onto_old_dense_l O hZF name hb ha hT hw hα q hq
  obtain ⟨m,succ,hm⟩ := hω.1.2 n hn
  obtain ⟨s,c,sm,sc,u,ur,uc⟩ := tree.level_l hZF O hω m hm r (below_trans_l O ha.1 hr hq)
  obtain ⟨β,t,βt,decision,below | incompatible⟩ := tree.decision_l hZF hω sc sm hn succ
  all_goals
    have cb := tree.below s c sc
    have ua := below_trans_l O ha.1 (below_trans_l O hq.1 ur hr) hq
    have αβ := old_value_unique_l O hZF name.1 ha.1 hb ua (below_trans_l O hb ua ha)
      (old_value_lower_l O hZF hb name.1.2.2.1 r u hr.1 ur value)
      (old_value_lower_l O hZF hb name.1.2.2.1 c u cb.1 ⟨ur.1,ur.2.1,uc⟩ decision)
    have tq := enum.1.2 α t q (αβ.symm ▸ βt) αq
    subst t
  · exact ⟨s,c,sc,cb.1,cb.2.1,below⟩
  · exact (incompatible ⟨u,⟨ur.1,ur.2.1,uc⟩,(below_trans_l O hq.1 ur hr).2.2⟩).elim

end YesMetaZFC.Model.Forcing.Internal

/-! ## Kripke 树的前缀保序与不相容性

全部归纳都量化原模型的有限历史。各层反链保证相容节点具有可比较前缀，
从而得到稠密映射所需的不相容性反射。
-/
namespace YesMetaZFC.Model.Forcing.Internal
open SetTheory SetTheory.Definitional.Project SetTheory.Descriptive
universe u
variable {M : Structure.{u}} (hZF : M.Models ZF)
local notation "I" => kpair_interpretation_l M (And.left hZF) (KP.exists_pair (ZF.modelsKP hZF))
variable {B R z a b f E ω κ F Γ : M.Domain} (O : Cond_order_d M B R z) (hω : M.IsOmega ω)
include hω

private theorem prefix_end_l (space : Fseq_space_d I ω κ F) {s t u α : M.Domain}
    (hs : M.mem s F) (ht : M.mem t F) (hu : M.mem u F) (end' : Fseq_end_d I ω u t α)
    (su : M.MemberSubset s u) : M.MemberSubset s t ∨ s = u := by
  obtain ⟨n,hn,sn⟩ := (space s).mp hs
  obtain ⟨m,hm,tm⟩ := (space t).mp ht
  obtain ⟨l,hl,ul⟩ := (space u).mp hu
  obtain ⟨l',m',decomp⟩ := end'
  have eq := decomp.source.2.2.2.eq hZF.1 ul.2.1
  subst l'
  have eq := decomp.prefix_sequence.2.2.2.eq hZF.1 tm.2.1
  subst m'
  have rs := (ds_restrict_iff_l I sn ul.1).mpr su
  rcases (hω.isOrdinal (ZF.modelsKP hZF)).wellOrder.linear.compare n hn m hm with same | nm | mn
  · exact Or.inl (ds_prefix_mono_l I sn tm.1 rs decomp.prefix_restriction (fun i hi => (same i).mp hi))
  · exact Or.inl (ds_prefix_mono_l I sn tm.1 rs decomp.prefix_restriction
      ((hω.members_areOrdinals (ZF.modelsKP hZF) m hm).transitive n nm))
  · have ln : M.MemberSubset l n := fun i hi => ((decomp.length_successor i).mp hi).elim
      (fun im => (hω.members_areOrdinals (ZF.modelsKP hZF) n hn).transitive m mn i im)
      (fun eq => (hZF.1.eq_of_same_members i m eq).symm ▸ mn)
    have us := ds_prefix_mono_l I ul sn.1 ((ds_restrict_iff_l I ul ul.1).mpr (fun _ hi => hi)) rs ln
    exact Or.inr (hZF.1.eq_of_same_members s u (fun i => ⟨su i,us i⟩))

include O

theorem Kr_tree_d.mono_l (tree : Kr_tree_d hZF B R z a b f E ω κ F Γ)
    {s t q r : M.Domain} (sq : Entry_d M s q Γ) (tr : Entry_d M t r Γ) (sub : M.MemberSubset s t) : Entry_d M r q R := by
  let ρ : Env M 3 := ⟨fun i => [F,Γ,R].get i,fun _ => a⟩
  let φ : UnarySchema 3 := { body := set[4] ⟪∀ s ∈ ⌜(.bound 1 : Term 4)⌝ₛ,
    s ⊆ ⌜(.newest : Term 4)⌝ₛ → ∀ q r,
    ⌜entry_m⌝ₚ(s,q,⌜(.bound 2 : Term 4)⌝ₛ) → ⌜entry_m⌝ₚ(⌜(.newest : Term 4)⌝ₛ,r,⌜(.bound 2 : Term 4)⌝ₛ) →
      ⌜entry_m⌝ₚ(r,q,⌜(.bound 3 : Term 4)⌝ₛ)⟫ }
  have sat t : φ.denote ρ t ↔ ∀ s, M.mem s F → M.MemberSubset s t → ∀ q r,
      Entry_d M s q Γ → Entry_d M t r Γ → Entry_d M r q R := by
    simp only [φ,UnarySchema.denote,Formula.satisfies_forallMem_iff,Formula.satisfies_imp_iff,
      Formula.satisfies_forall_iff,Formula.satisfies_subset_iff,entry_sat_l M hZF.1,Definitional.Term.eval_weaken]
    rfl
  have all := history_ind_l hZF hω tree.space φ ρ (fun e empty => (sat e).mpr (by
    intro s _ sub q r sq er
    have eq := hZF.1.eq_of_same_members s e (fun x => iff_of_false (fun hx => empty x (sub x hx)) (empty x))
    have qr := tree.function.1.2 e q r (eq ▸ sq) er
    exact qr.symm ▸ O.refl r (tree.below e r er).1)) (by
    intro t u α ht hu _ end' ih
    apply (sat u).mpr
    intro s hs sub q r sq ur
    rcases prefix_end_l hZF hω tree.space hs ht hu end' sub with st | eq
    · obtain ⟨n,_,tn⟩ := (tree.space t).mp ht
      obtain ⟨c,_,tc⟩ := tree.function.2.2 t ht
      obtain ⟨J,branch,children⟩ := tree.children t c n tc tn
      have rc := (branch.below α r ((children u α r hu end').mp ur)).1
      exact O.trans r c q rc.1 (tree.below t c tc).1 (tree.below s q sq).1 rc.2.2
        ((sat t).mp ih s hs st q c sq tc)
    · have qr := tree.function.1.2 u q r (eq ▸ sq) ur
      exact qr.symm ▸ O.refl r (tree.below u r ur).1)
  exact (sat t).mp (all t (tree.function.input_mem_of_pairMember tr)) s (tree.function.input_mem_of_pairMember sq) sub q r sq tr

theorem Kr_tree_d.level_injective_l (tree : Kr_tree_d hZF B R z a b f E ω κ F Γ) :
    ∀ n, M.mem n ω → ∀ s t q r, M.IsSetFunctionFromTo I s n κ → M.IsSetFunctionFromTo I t n κ →
      Entry_d M s q Γ → Entry_d M t r Γ → Cmp_d M B R z q r → s = t := by
  let ρ : Env M 5 := ⟨fun i => [κ,Γ,B,R,z].get i,fun _ => a⟩
  let φ : UnarySchema 5 := { body := set[6] ⟪∀ s t q r,
    ⌜(Formula.isFunctionFromTo kpair_convention_l)⌝ₚ(s,⌜(.newest : Term 6)⌝ₛ,⌜(.bound 1 : Term 6)⌝ₛ) →
    ⌜(Formula.isFunctionFromTo kpair_convention_l)⌝ₚ(t,⌜(.newest : Term 6)⌝ₛ,⌜(.bound 1 : Term 6)⌝ₛ) →
    ⌜entry_m⌝ₚ(s,q,⌜(.bound 2 : Term 6)⌝ₛ) → ⌜entry_m⌝ₚ(t,r,⌜(.bound 2 : Term 6)⌝ₛ) →
    ⌜cmp_m⌝ₚ(⌜(.bound 3 : Term 6)⌝ₛ,⌜(.bound 4 : Term 6)⌝ₛ,⌜(.bound 5 : Term 6)⌝ₛ,q,r) → s = t⟫ }
  have sat n : φ.denote ρ n ↔ ∀ s t q r, M.IsSetFunctionFromTo I s n κ → M.IsSetFunctionFromTo I t n κ →
      Entry_d M s q Γ → Entry_d M t r Γ → Cmp_d M B R z q r → s = t := by
    simp only [φ,UnarySchema.denote,Formula.satisfies_forall_iff,Formula.satisfies_imp_iff,
      Formula.satisfies_isFunctionFromTo_iff I hZF.1,entry_sat_l M hZF.1,cmp_sat_l M hZF.1,
      Formula.satisfies_extensionalEq_iff_eq hZF.1,Definitional.Term.eval_weaken]
    rfl
  apply hω.induction
  · obtain ⟨A,member⟩ := ZF.separation_exists_d hZF φ ρ ω
    exact ⟨A,fun n => (member n).trans (and_congr_right fun _ => sat n)⟩
  · intro o empty s t _ _ fs ft _ _ _
    have no {s} (fs : M.IsSetFunctionFromTo I s o κ) x (hx : M.mem x s) : False := by
      obtain ⟨i,y,pair⟩ := fs.1.1 x hx
      exact empty i (fs.input_mem_of_pairMember ⟨x,pair,hx⟩)
    exact hZF.1.eq_of_same_members s t (fun x => iff_of_false (no fs x) (no ft x))
  · intro n hn ih m succ s t q r fs ft sq tr compat
    obtain ⟨m',succ',hm⟩ := hω.1.2 n hn
    have hm : M.mem m ω := succ'.eq hZF.1 succ ▸ hm
    have split {s} (fs : M.IsSetFunctionFromTo I s m κ) : ∃ u α,
        M.IsSetFunctionFromTo I u n κ ∧ Fseq_end_d I ω s u α := by
      obtain ⟨u,cut⟩ := ZF.exists_restriction hZF I s n
      have un := cut.isSetFunctionFromTo fs (fun i hi => (succ i).mpr (Or.inl hi))
      obtain ⟨α,_,nα⟩ := fs.2.2 n succ.predecessor_mem
      exact ⟨u,α,un,m,n,⟨hm,hω.members_areOrdinals (ZF.modelsKP hZF) m hm,fs.1,fs.2.1⟩,
        hn,succ,⟨hn,hω.members_areOrdinals (ZF.modelsKP hZF) n hn,un.1,un.2.1⟩,cut,nα⟩
    obtain ⟨u,α,un,su⟩ := split fs
    obtain ⟨v,β,vn,tv⟩ := split ft
    obtain ⟨c,_,uc⟩ := tree.function.2.2 u ((tree.space u).mpr ⟨n,hn,un⟩)
    obtain ⟨d,_,vd⟩ := tree.function.2.2 v ((tree.space v).mpr ⟨n,hn,vn⟩)
    have qc := tree.mono_l hZF O hω uc sq (su.subset_l I)
    have rd := tree.mono_l hZF O hω vd tr (tv.subset_l I)
    obtain ⟨w,wq,wr⟩ := compat
    have uv := ih u v c d un vn uc vd ⟨w,
      ⟨wq.1,wq.2.1,O.trans w q c wq.1 (tree.below s q sq).1 (tree.below u c uc).1 wq.2.2 qc⟩,
      O.trans w r d wq.1 (tree.below t r tr).1 (tree.below v d vd).1 wr rd⟩
    subst v
    have cd := tree.function.1.2 u c d uc vd
    subst d
    obtain ⟨J,branch,children⟩ := tree.children u c n uc un
    have αβ := branch.separate α β q r
      ((children s α q (tree.function.input_mem_of_pairMember sq) su).mp sq)
      ((children t β r (tree.function.input_mem_of_pairMember tr) tv).mp tr) ⟨w,wq,wr⟩
    exact fseq_end_rebuild_l I hZF.1 su (αβ.symm ▸ tv)

theorem Kr_tree_d.compat_l (tree : Kr_tree_d hZF B R z a b f E ω κ F Γ)
    {s t q r : M.Domain} (sq : Entry_d M s q Γ) (tr : Entry_d M t r Γ) :
    Cmp_d M B R z q r ↔ M.MemberSubset s t ∨ M.MemberSubset t s := by
  obtain ⟨n,hn,sn⟩ := (tree.space s).mp (tree.function.input_mem_of_pairMember sq)
  obtain ⟨m,hm,tm⟩ := (tree.space t).mp (tree.function.input_mem_of_pairMember tr)
  have short {s t q r n m} (sn : M.IsSetFunctionFromTo I s n κ) (tm : M.IsSetFunctionFromTo I t m κ)
      (hn : M.mem n ω) (sq : Entry_d M s q Γ) (tr : Entry_d M t r Γ)
      (nm : M.MemberSubset n m) (compat : Cmp_d M B R z q r) : M.MemberSubset s t := by
    obtain ⟨u,cut⟩ := ZF.exists_restriction hZF I t n
    have un := cut.isSetFunctionFromTo tm nm
    obtain ⟨c,_,uc⟩ := tree.function.2.2 u ((tree.space u).mpr ⟨n,hn,un⟩)
    have ut := (ds_restrict_iff_l I un tm.1).mp cut
    have rc := tree.mono_l hZF O hω uc tr ut
    obtain ⟨v,vq,vr⟩ := compat
    have eq := tree.level_injective_l hZF O hω n hn s u q c sn un sq uc
      ⟨v,vq,O.trans v r c vq.1 (tree.below t r tr).1 (tree.below u c uc).1 vr rc⟩
    exact eq.symm ▸ ut
  constructor
  · intro compat
    rcases (hω.isOrdinal (ZF.modelsKP hZF)).wellOrder.linear.compare n hn m hm with same | nm | mn
    · exact Or.inl (short sn tm hn sq tr (fun i hi => (same i).mp hi) compat)
    · exact Or.inl (short sn tm hn sq tr ((hω.members_areOrdinals (ZF.modelsKP hZF) m hm).transitive n nm) compat)
    · obtain ⟨v,vq,vr⟩ := compat
      exact Or.inr (short tm sn hm tr sq ((hω.members_areOrdinals (ZF.modelsKP hZF) n hn).transitive m mn)
        ⟨v,⟨vq.1,vq.2.1,vr⟩,vq.2.2⟩)
  · rintro (st | ts)
    · have hr := tree.below t r tr
      exact ⟨r,⟨hr.1,hr.2.1,tree.mono_l hZF O hω sq tr st⟩,O.refl r hr.1⟩
    · have hq := tree.below s q sq
      exact ⟨q,below_refl_l O hq.1 hq.2.1,tree.mono_l hZF O hω tr sq ts⟩

end YesMetaZFC.Model.Forcing.Internal

/-! ## κ 有限序列到原正锥的实际稠密映射 -/
namespace YesMetaZFC.Model.Forcing.Internal
open SetTheory SetTheory.Definitional.Project
universe u
variable {M : Structure.{u}} (hZFC : M.Models ZFC)
local notation "hZF" => ZFC.models_zf_l hZFC
local notation "I" => kpair_interpretation_l M (And.left hZFC) (KP.exists_pair (ZF.modelsKP hZF))

theorem kripke_map_l {B R z a b T w f ω κ : M.Domain} (O : Cond_order_d M B R z)
    (hω : M.IsOmega ω) (hκ : M.IsUncountableCardinal I ω κ) (size : M.CardinalLessOrEqual I B κ)
    (name : Onto_name_d B R z a T w f) (hb : M.mem b B) (ha : Below_d M B R z a b)
    (hT : Check_d M b ω T) (hw : Check_d M b κ w) : ∃ C F S Γ,
      (∀ p, M.mem p C ↔ Below_d M B R z p a) ∧ Cond_order_d M C R z ∧
      Fseq_space_d I ω κ F ∧ (∀ s t, Entry_d M s t S ↔ M.mem s F ∧ M.mem t F ∧ M.MemberSubset t s) ∧
      Cond_order_d M F S F ∧ Dmap_d F S F C R z Γ := by
  obtain ⟨J,inj⟩ := size
  obtain ⟨E,enum,retract⟩ := ZF.injection_retract_l I hZF inj (fun _ h => h) ha.1
  have onto : M.IsSetSurjectiveOnto I E κ B := by
    intro q hq
    obtain ⟨α,hα,qα⟩ := inj.1.2.2 q hq
    exact ⟨α,hα,retract q α qα⟩
  obtain ⟨F,Γ,tree⟩ := kr_tree_l hZF hZFC O hω hκ ⟨J,inj⟩ name hb ha hT hw enum
  obtain ⟨S,order,source,_⟩ := subset_order_l M hZF F
  let ρ : Env M 4 := ⟨fun i => [B,R,z,a].get i,fun _ => a⟩
  let φ : UnarySchema 4 := { body := below_m (.bound 1) (.bound 2) (.bound 3) .newest (.bound 4) }
  obtain ⟨C,members⟩ := ZF.separation_exists_d hZF φ ρ B
  have cone p : M.mem p C ↔ Below_d M B R z p a :=
    ((members p).trans (and_congr_right fun _ => below_sat_l M hZF.1 ..)).trans ⟨And.right,fun h => ⟨h.1,h⟩⟩
  have target : Cond_order_d M C R z := {
    refl := fun p hp => O.refl p ((cone p).mp hp).1
    trans := fun p q r hp hq hr pq qr => O.trans p q r ((cone p).mp hp).1 ((cone q).mp hq).1 ((cone r).mp hr).1 pq qr
    zero := fun p hp pz => O.zero p ((cone p).mp hp).1 pz }
  have nonzero p (hp : M.mem p F) : p ≠ F := fun eq => KP.mem_irrefl_d (ZF.modelsKP hZF) F (eq ▸ hp)
  refine ⟨C,F,S,Γ,cone,target,tree.space,order,source,⟨?_,?_,tree.function.1.2,?_,?_,?_⟩⟩
  · intro s hs _
    obtain ⟨q,_,sq⟩ := tree.function.2.2 s hs
    exact ⟨q,sq⟩
  · intro s q sq
    have hs := tree.function.input_mem_of_pairMember sq
    exact ⟨⟨hs,nonzero s hs⟩,(cone q).mpr (tree.below s q sq),(tree.below s q sq).2.1⟩
  · intro s t q r sq tr st
    exact tree.mono_l hZF O hω tr sq ((order s t).mp st).2.2
  · intro s t q r sq tr compat
    obtain ⟨v,vq,vr⟩ := compat
    have compat := (tree.compat_l hZF O hω sq tr).mp ⟨v,⟨((cone v).mp vq.1).1,vq.2.1,vq.2.2⟩,vr⟩
    have hs := tree.function.input_mem_of_pairMember sq
    have ht := tree.function.input_mem_of_pairMember tr
    rcases compat with st | ts
    · exact ⟨t,⟨ht,nonzero t ht,(order t s).mpr ⟨ht,hs,st⟩⟩,source.refl t ht⟩
    · exact ⟨s,below_refl_l source hs (nonzero s hs),(order s t).mpr ⟨hs,ht,ts⟩⟩
  · intro q hq _
    obtain ⟨s,c,sc,cq⟩ := tree.dense_l hZF O hω name hb ha hT hw enum onto q ((cone q).mp hq)
    exact ⟨s,c,sc,cq.2.2⟩

end YesMetaZFC.Model.Forcing.Internal
