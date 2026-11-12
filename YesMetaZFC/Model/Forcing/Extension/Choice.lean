import YesMetaZFC.Model.Forcing.Truth.Definability
import YesMetaZFC.Model.Forcing.Names.PairConstruction
import YesMetaZFC.Model.Forcing.Check.SupportBound
import YesMetaZFC.SetTheory.Ord.Natural
import YesMetaZFC.Model.Forcing.Extension.Isomorphism
import YesMetaZFC.Model.Forcing.Maximum.Bounded
import YesMetaZFC.Model.SmallGraph.ZFC

/-! # 实际地模型泛型滤子实例

二元布尔条件在原小图 ZFC 模型中编码，顶原子的主滤子遇到该模型的每个稠密集。
该实例验证内部泛型接口；不把它称为无原子 Cohen 力迫的泛型滤子。
-/

namespace YesMetaZFC.Model.Forcing.Internal
open SmallGraph
attribute [local implicit_reducible] sg_model SetTheory.Definitional.Project.FirstOrderSemantics.reduct

def two_code_l : Bool → WF_graph.{0}
  | false => WF_graph.empty
  | true => WF_graph.root_sum (fun _ : PUnit => WF_graph.empty)

theorem two_ne_l : SG_set.mk (two_code_l true) ≠ SG_set.mk (two_code_l false) := by
  intro h
  have hm : SG_set.empty ∈ SG_set.mk (two_code_l true) :=
    (SG_set.mem_sum _ _).mpr ⟨PUnit.unit, rfl⟩
  exact SG_set.not_mem_empty _ (h ▸ hm)

theorem two_code_injective_l : Function.Injective (fun b => SG_set.mk (two_code_l b)) := by
  intro a b h
  cases a <;> cases b
  · rfl
  · exact False.elim (two_ne_l h.symm)
  · exact False.elim (two_ne_l h)
  · rfl

def two_order_l : PO_pre Bool where
  le a b := a = false ∨ b = true
  le_refl a := by cases a <;> simp
  le_trans := by intro a b c h k; cases a <;> cases b <;> cases c <;> simp_all

def two_conditions_l : SG_set.{0} := condition_set_l two_code_l
def two_relation_l : SG_set.{0} := order_set_l two_order_l.le two_code_l
def two_zero_l : SG_set.{0} := SG_set.mk (two_code_l false)
def two_one_l : SG_set.{0} := SG_set.mk (two_code_l true)

theorem two_cond_order_l : Cond_order_d sg_structure two_conditions_l two_relation_l two_zero_l where
  refl p hp := by
    obtain ⟨a, rfl⟩ := (SG_set.mem_sum two_code_l p).mp hp
    exact (order_mem_l two_order_l.le two_code_l two_code_injective_l a a).mpr (two_order_l.le_refl a)
  trans p q r hp hq hr h k := by
    obtain ⟨a, rfl⟩ := (SG_set.mem_sum two_code_l p).mp hp
    obtain ⟨b, rfl⟩ := (SG_set.mem_sum two_code_l q).mp hq
    obtain ⟨c, rfl⟩ := (SG_set.mem_sum two_code_l r).mp hr
    exact (order_mem_l two_order_l.le two_code_l two_code_injective_l a c).mpr
      (two_order_l.le_trans ((order_mem_l _ _ two_code_injective_l a b).mp h)
        ((order_mem_l _ _ two_code_injective_l b c).mp k))
  zero p hp hz := by
    obtain ⟨a, rfl⟩ := (SG_set.mem_sum two_code_l p).mp hp
    have h := (order_mem_l two_order_l.le two_code_l two_code_injective_l a false).mp hz
    have ha : a = false := h.elim id (fun h => Bool.noConfusion h)
    exact congrArg (fun a => SG_set.mk (two_code_l a)) ha

def two_filter_l (p : SG_set.{0}) : Prop :=
  p ∈ two_conditions_l ∧ Entry_d sg_structure two_one_l p two_relation_l

theorem two_generic_l : Generic_d sg_structure two_conditions_l two_relation_l two_zero_l two_filter_l := by
  apply generic_atom_l two_cond_order_l
    (a := two_one_l) ((SG_set.mem_sum two_code_l _).mpr ⟨true, rfl⟩) two_ne_l
  intro p hp
  obtain ⟨a, rfl⟩ := (SG_set.mem_sum two_code_l p).mp hp.1
  cases a
  · exact False.elim (hp.2.1 rfl)
  · exact two_cond_order_l.refl _ ((SG_set.mem_sum two_code_l _).mpr ⟨true, rfl⟩)

end YesMetaZFC.Model.Forcing.Internal

/-! ## 内部名称扩张的全收集模式

在“源子名称 × 条件集”上，内部收集为每个能够力迫见证的条件选取一个名称。
无见证的输入用空名称处理；随后分离有效名称并统一加上一个被接受的标签。
-/

namespace YesMetaZFC.Model.Forcing.Internal
open SetTheory SetTheory.Definitional.Project
universe u

variable {M : SetTheory.Structure.{u}} {B R z : M.Domain} {U : M.Domain → Prop}
variable (O : Cond_order_d M B R z) (hZF : M.Models ZF) (hU : Generic_d M B R z U)

local notation "E" => extension_l M hZF B R z U
include O hZF hU

theorem internal_collection_l {n} (φ : BinarySchema n) (η : Env E n) (A : (E).Domain)
    (h : ∀ x : (E).Domain, x ∈ A → ∃ y : (E).Domain,
      Formula.satisfies ((η.push x).push y) φ.body) :
    ∃ C : (E).Domain, ∀ x : (E).Domain, x ∈ A → ∃ y : (E).Domain,
      y ∈ C ∧ Formula.satisfies ((η.push x).push y) φ.body := by
  classical
  obtain ⟨ρ, hρ⟩ := lift_env_l hZF η
  obtain ⟨t, ht, hA⟩ := value_name_l A
  obtain ⟨S, htS, hS⟩ := ht
  let I := kpair_interpretation_l M hZF.1 (KP.exists_pair (ZF.modelsKP hZF))
  obtain ⟨K, hK⟩ := ZF.exists_cartesianProduct hZF I S B
  obtain ⟨e, he⟩ := KP.exists_empty (ZF.modelsKP hZF)
  have hen := name_empty_l M (KP.exists_pair (ZF.modelsKP hZF)) B e he
  let δ := ((ρ.push B).push R).push z
  let es : Fin n → Term (n + 7) := fun i => .bound ⟨i.val + 7, by omega⟩
  let χ : UnarySchema (n+1) := { body := φ.body, freeClosed := φ.freeClosed }
  let ψ : BinarySchema (n + 3) := {
    body := .existsE (.existsE (.conj (kpair_m (.bound 3) (.bound 1) .newest)
      (witness_m χ (Fin.cases (.bound 1) es) (.bound 6) (.bound 5) (.bound 4) .newest (.bound 2))))
    freeClosed := by
      simp -implicitDefEqProofs [Definitional.Formula.FreeClosed, es]
      apply witness_closed_l
      · exact Fin.cases rfl (fun _ => rfl)
      all_goals rfl }
  have hψ k v : ψ.denote δ k v ↔ ∃ a p, KPair_d M k a p ∧ Name_d M B v ∧
      ∀ w, Name_d M B w → Forces_d M B R z φ.body ((ρ.push a).push w) p →
        Forces_d M B R z φ.body ((ρ.push a).push v) p := by
    have hs a p : (⟨fun i => (es i).eval ((((δ.push k).push v).push a).push p),
        ((((δ.push k).push v).push a).push p).free⟩ : Env M n) = ρ := by cases ρ; rfl
    simp only [BinarySchema.denote, ψ, Formula.satisfies_exists_iff, Formula.satisfies_conj_iff,
      kpair_sat_l M hZF.1, witness_sat_l hZF.1, args_cons_l, hs]
    rfl
  obtain ⟨T, hT⟩ := ZF.collection_exists_d hZF ψ δ K (fun k hk => by
    obtain ⟨a, _, p, _, hk⟩ := (hK k).mp hk
    by_cases h : ∃ v, Name_d M B v ∧ Forces_d M B R z φ.body ((ρ.push a).push v) p
    · obtain ⟨v, hv, hφ⟩ := h
      exact ⟨v, (hψ k v).mpr ⟨a, p, hk, hv, fun _ _ _ => hφ⟩⟩
    · exact ⟨e, (hψ k e).mpr ⟨a, p, hk, hen, fun v hv hφ => False.elim (h ⟨v, hv, hφ⟩)⟩⟩)
  let ρB : Env M 1 := ⟨fun _ => B, fun _ => B⟩
  let ν : UnarySchema 1 := { body := name_m (.bound 1) (.bound 0) }
  obtain ⟨F, hF⟩ := ZF.separation_exists_d hZF ν ρB T
  have hf v : M.mem v F ↔ M.mem v T ∧ Name_d M B v :=
    (hF v).trans (and_congr_right fun _ => name_sat_l M hZF.1 (ρB.push v) (.bound 1) (.bound 0))
  obtain ⟨b, hb⟩ := hU.inhabited
  let ρb : Env M 1 := ⟨fun _ => b, fun _ => b⟩
  obtain ⟨q, hq, _, hqE⟩ := name_comp_l M hZF BinarySchema.constantValue ρb B F
    (fun v hv => ((hf v).mp hv).2)
  obtain ⟨C, hC⟩ := name_value_l (R := R) (z := z) (U := U) hq
  refine ⟨C, fun x hx => ?_⟩
  obtain ⟨a, c, ha, hc, hax⟩ := (qval_mem_l O hZF hU hA).mp hx
  obtain ⟨y, hxy⟩ := h x hx
  obtain ⟨v, hv, hvy⟩ := value_name_l y
  have hρ' := env_val_push_l hZF (env_val_push_l hZF hρ hax) hvy
  have hEval := formula_eval_l O hZF hU φ.body φ.freeClosed ((ρ.push a).push v)
    ((η.push x).push y) hρ'
  obtain ⟨p, hp, hpφ⟩ := hEval.2.mpr hxy
  obtain ⟨r, hr, _, hrp⟩ := hU.directed c p hc hp
  have hr' := hU.proper r hr
  have hrφ := hEval.1.1 p r (hU.proper p hp).1 ⟨hr'.1, hr'.2, hrp⟩ hpφ
  obtain ⟨k, hk⟩ := I.total a r
  obtain ⟨w, hwT, hw⟩ := hT k ((hK k).mpr ⟨a, (supp_entry_l M hS htS ha).1, r, hr'.1, hk⟩)
  obtain ⟨a', r', hk', hwN, hwφ⟩ := (hψ k w).mp hw
  obtain ⟨rfl, rfl⟩ := kpair_injective_l M hk hk'
  obtain ⟨y', hwy⟩ := name_value_l (R := R) (z := z) (U := U) hwN
  refine ⟨y', (qval_mem_l O hZF hU hC).mpr ⟨w, b, (hqE w b).mpr ⟨(hf w).mpr ⟨hwT, hwN⟩,
    (hU.proper b hb).1, (Formula.denote_constantValue_iff hZF.1 ρb w b).mpr rfl⟩, hb, hwy⟩, ?_⟩
  exact (forcing_truth_l O hZF hU φ.body φ.freeClosed ((ρ.push a).push w)
    ((η.push x).push y') (env_val_push_l hZF (env_val_push_l hZF hρ hax) hwy)).mp
      ⟨r, hr, hwφ v hv hrφ⟩

end YesMetaZFC.Model.Forcing.Internal

/-! ## 幂集保持：将扩张子集正规化为地模型有界名称

源名称的闭支撑 S 给出内部界 S×B。扩张中的每个子集都可用这个界的一个内部
子集名称表示；模型的幂集公理因此足以收集全部扩张子集，不取宿主的全幂集。
-/

namespace YesMetaZFC.Model.Forcing.Internal
open SetTheory SetTheory.Definitional.Project SmallGraph
universe u
variable (M : SetTheory.Structure.{u})

def Sub_name_d (R t s : M.Domain) : Prop := ∀ a b, Entry_d M a b s → Source_d M R t a b

def sub_name_m {n} (R t s : Term n) : Formula 1 n :=
  .forallE (.forallE (.imp (entry_m (.bound 1) .newest s.weaken.weaken)
    (source_m R.weaken.weaken t.weaken.weaken (.bound 1) .newest)))
derive_free_closed sub_name_m

theorem sub_name_sat_l (hE : Extensional M) {n} (ρ : Env M n) (R t s : Term n) :
    Formula.satisfies ρ (sub_name_m R t s) ↔ Sub_name_d M (R.eval ρ) (t.eval ρ) (s.eval ρ) := by
  simp only [sub_name_m, Sub_name_d, Formula.satisfies_forall_iff, Formula.satisfies_imp_iff,
    entry_sat_l M hE, source_sat_l M hE, Definitional.Term.eval_newest, Definitional.Term.eval_weaken,
    Term.eval_bound_zero_push, Term.eval_bound_one_push]

theorem sub_name_val_l {M : SetTheory.Structure.{u}} {B R z} {U : M.Domain → Prop}
    (O : Cond_order_d M B R z) (hZF : M.Models ZF) (hU : Generic_d M B R z U)
    {s t} {x y : Name_quot_l M B R z U} (hs : Qval_d M B R z U s x) (ht : Qval_d M B R z U t y)
    (h : Sub_name_d M R t s) : ∀ w, w ∈ x → w ∈ y := by
  intro w hw
  obtain ⟨a, b, ha, hb, hv⟩ := (qval_mem_l O hZF hU hs).mp hw
  exact source_val_l O hZF hU ht hv (h a b ha) hb

variable {M} {B R z : M.Domain} {U : M.Domain → Prop}
  (O : Cond_order_d M B R z) (hZF : M.Models ZF) (hU : Generic_d M B R z U)

include O hZF hU

/-- 子集名称只使用原支撑中的子名称；每个系数加强某个原成员系数。 -/
theorem normalize_name_l {S s t} (hS : Supp_d M B S) (htS : M.mem t S)
    {x y : Name_quot_l M B R z U} (hs : Qval_d M B R z U s x) (ht : Qval_d M B R z U t y)
    (hxy : ∀ w, w ∈ x → w ∈ y) :
    ∃ q, Name_d M B q ∧
      (∀ p, M.mem p q → ∃ a b, M.mem a S ∧ M.mem b B ∧ KPair_d M p a b) ∧
      Sub_name_d M R t q ∧ Qval_d M B R z U q x := by
  let δ : Env M 5 := ((((⟨fun _ => B, fun _ => B⟩ : Env M 1).push R).push z).push t).push s
  let φ : BinarySchema 5 := {
    body := .conj (source_m (.bound 5) (.bound 3) (.bound 1) (.bound 0))
      (mem_force_m (.bound 6) (.bound 5) (.bound 4) (.bound 0) (.bound 1) (.bound 2)) }
  have hφ a b : φ.denote δ a b ↔ Source_d M R t a b ∧ Mem_force_d M B R z b a s := by
    simp only [BinarySchema.denote, φ, Formula.satisfies_conj_iff, source_sat_l M hZF.1,
      mem_force_sat_l M hZF.1]
    rfl
  obtain ⟨q, hq, hqmem, he⟩ := name_comp_l M hZF φ δ B S (fun a ha => ⟨S, ha, hS⟩)
  obtain ⟨w, hw⟩ := name_value_l (R := R) (z := z) (U := U) hq
  have hwx : w = x := by
    apply (extension_ext_l O hZF hU).eq_of_same_members
    intro a
    constructor
    · intro ha
      obtain ⟨b, p, hb, hp, hbv⟩ := (qval_mem_l O hZF hU hw).mp ha
      exact (qval_mem_forcing_l O hZF hU hbv hs).mp ⟨p, hp, ((hφ b p).mp ((he b p).mp hb).2.2).2⟩
    · intro ha
      obtain ⟨b, c, hb, hc, hbv⟩ := (qval_mem_l O hZF hU ht).mp (hxy a ha)
      obtain ⟨p, hp, hmem⟩ := (qval_mem_forcing_l O hZF hU hbv hs).mpr ha
      obtain ⟨d, hd, hdc, hdp⟩ := hU.directed c p hc hp
      have hd' := hU.proper d hd
      have hmem' := (regular_mem_l O b s).1 p d (hU.proper p hp).1 ⟨hd'.1, hd'.2, hdp⟩ hmem
      exact (qval_mem_l O hZF hU hw).mpr ⟨b, d, (he b d).mpr
        ⟨(supp_entry_l M hS htS hb).1, hd'.1, (hφ b d).mpr ⟨⟨c, hb, hdc⟩, hmem'⟩⟩, hd, hbv⟩
  refine ⟨q, hq, ?_, ?_, hwx ▸ hw⟩
  · intro p hp
    obtain ⟨a, b, ha, hb, h, _⟩ := (hqmem p).mp hp
    exact ⟨a, b, ha, hb, h⟩
  · exact fun a b h => ((hφ a b).mp ((he a b).mp h).2.2).1

local notation "E" => extension_l M hZF B R z U

theorem internal_power_l (A : (E).Domain) : ∃ P : (E).Domain, ∀ X : (E).Domain,
    X ∈ P ↔ ∀ Y : (E).Domain, Y ∈ X → Y ∈ A := by
  obtain ⟨t, ht, hA⟩ := value_name_l A
  obtain ⟨S, htS, hS⟩ := ht
  let I := kpair_interpretation_l M hZF.1 (KP.exists_pair (ZF.modelsKP hZF))
  obtain ⟨T, hT⟩ := ZF.exists_cartesianProduct hZF I S B
  obtain ⟨K, hK⟩ := ZF.exists_powerSet hZF T
  have hk s (hs : M.mem s K) : Name_d M B s := by
    apply name_adjoin_l M (KP.exists_pair (ZF.modelsKP hZF)) (KP.exists_union (ZF.modelsKP hZF)) hS
    intro p hp
    obtain ⟨a, ha, b, hb, h⟩ := (hT p).mp ((hK s).mp hs p hp)
    exact ⟨a, b, h, ha, hb⟩
  obtain ⟨b, hb⟩ := hU.inhabited
  let δ : Env M 3 := ((⟨fun _ => t, fun _ => t⟩ : Env M 1).push R).push b
  let φ : BinarySchema 3 := {
    body := .conj (Formula.extensionalEq (.bound 0) (.bound 2))
      (sub_name_m (.bound 3) (.bound 4) (.bound 1)) }
  have hφ s p : φ.denote δ s p ↔ p = b ∧ Sub_name_d M R t s := by
    simp only [BinarySchema.denote, φ, Formula.satisfies_conj_iff,
      Formula.satisfies_extensionalEq_iff_eq hZF.1, sub_name_sat_l M hZF.1]
    rfl
  obtain ⟨q, hq, _, he⟩ := name_comp_l M hZF φ δ B K hk
  obtain ⟨P, hP⟩ := name_value_l (R := R) (z := z) (U := U) hq
  refine ⟨P, fun X => ?_⟩
  constructor
  · intro hX Y hY
    obtain ⟨s, p, hs, _, hsv⟩ := (qval_mem_l O hZF hU hP).mp hX
    exact sub_name_val_l O hZF hU hsv hA ((hφ s p).mp ((he s p).mp hs).2.2).2 Y hY
  · intro hX
    obtain ⟨s, _, hsv⟩ := value_name_l X
    obtain ⟨s', _, hs', hst, hv⟩ := normalize_name_l O hZF hU hS htS hsv hA hX
    have hsK : M.mem s' K := (hK s').mpr (fun p hp => by
      obtain ⟨a, c, ha, hc, h⟩ := hs' p hp
      exact (hT p).mpr ⟨a, ha, c, hc, h⟩)
    exact (qval_mem_l O hZF hU hP).mpr ⟨s', b, (he s' b).mpr
      ⟨hsK, (hU.proper b hb).1, (hφ s' b).mpr ⟨rfl, hst⟩⟩, hb, hv⟩

end YesMetaZFC.Model.Forcing.Internal

/-! ## 内部名称扩张的全分离模式

从源名称的闭支撑中分离出带权子名称，权重同时加强原成员系数并力迫原分离正文。
真值定理在两个方向上给出精确成员刻画。
-/

namespace YesMetaZFC.Model.Forcing.Internal
open SetTheory SetTheory.Definitional.Project
universe u
variable {M : SetTheory.Structure.{u}} {B R z : M.Domain} {U : M.Domain → Prop}
variable (O : Cond_order_d M B R z) (hZF : M.Models ZF) (hU : Generic_d M B R z U)

local notation "E" => extension_l M hZF B R z U
include O hZF hU

theorem internal_separation_l {n} (φ : UnarySchema n) (η : Env E n) (A : (E).Domain) :
    ∃ C : (E).Domain, ∀ x : (E).Domain,
      x ∈ C ↔ x ∈ A ∧ Formula.satisfies (η.push x) φ.body := by
  obtain ⟨ρ, hρ⟩ := lift_env_l hZF η
  obtain ⟨t, ht, hA⟩ := value_name_l A
  obtain ⟨S, htS, hS⟩ := ht
  let δ := (((ρ.push t).push B).push R).push z
  let e : Fin (n + 1) → Term (n + 6) := Fin.cases (.bound 1) (fun i => .bound ⟨i.val + 6, by omega⟩)
  let ψ : BinarySchema (n + 4) := {
    body := .conj (source_m (.bound 3) (.bound 5) (.bound 1) (.bound 0))
      (force_at_m φ.body e (.bound 4) (.bound 3) (.bound 2) (.bound 0))
    freeClosed := by
      have he : ∀ i, (e i).freeSupport = [] := Fin.cases rfl (fun _ => rfl)
      simp -implicitDefEqProofs [Definitional.Formula.FreeClosed, he, φ.freeClosed] }
  have hψ a p : ψ.denote δ a p ↔ Source_d M R t a p ∧ Forces_d M B R z φ.body (ρ.push a) p := by
    have he : (⟨fun i => (e i).eval ((δ.push a).push p), ((δ.push a).push p).free⟩ : Env M (n + 1)) = ρ.push a := by
      rw [Env.mk.injEq]
      constructor
      · funext i; exact Fin.cases rfl (fun _ => rfl) i
      · rfl
    simp only [BinarySchema.denote, ψ, Formula.satisfies_conj_iff, source_sat_l M hZF.1,
      force_at_sat_l, he]
    rfl
  obtain ⟨q, hq, _, he⟩ := name_comp_l M hZF ψ δ B S (fun s hs => ⟨S, hs, hS⟩)
  obtain ⟨C, hC⟩ := name_value_l (R := R) (z := z) (U := U) hq
  refine ⟨C, fun x => ?_⟩
  constructor
  · intro hx
    obtain ⟨a, p, ha, hp, hax⟩ := (qval_mem_l O hZF hU hC).mp hx
    obtain ⟨_, _, ha⟩ := (he a p).mp ha
    obtain ⟨ha, hφ⟩ := (hψ a p).mp ha
    exact ⟨source_val_l O hZF hU hA hax ha hp,
      (forcing_truth_l O hZF hU φ.body φ.freeClosed (ρ.push a) (η.push x)
        (env_val_push_l hZF hρ hax)).mp ⟨p, hp, hφ⟩⟩
  · rintro ⟨hx, hφ⟩
    obtain ⟨a, c, ha, hc, hax⟩ := (qval_mem_l O hZF hU hA).mp hx
    have ht := formula_eval_l O hZF hU φ.body φ.freeClosed (ρ.push a) (η.push x)
      (env_val_push_l hZF hρ hax)
    obtain ⟨p, hp, hφ⟩ := ht.2.mpr hφ
    obtain ⟨b, hb, hbc, hbp⟩ := hU.directed c p hc hp
    have hb' := hU.proper b hb
    have hφb := ht.1.1 p b (hU.proper p hp).1 ⟨hb'.1, hb'.2, hbp⟩ hφ
    exact (qval_mem_l O hZF hU hC).mpr ⟨a, b, (he a b).mpr
      ⟨(supp_entry_l M hS htS ha).1, hb'.1, (hψ a b).mpr ⟨⟨c, ha, hbc⟩, hφb⟩⟩, hb, hax⟩

end YesMetaZFC.Model.Forcing.Internal

/-! ## 内部名称扩张的配对、并集与无穷

有限配对使用对全部泛型统一的规范名称；并集同时加强两层成员的系数。
无穷公理解释地模型的归纳集，不预设内部 ω 等于宿主 ω。
-/

namespace YesMetaZFC.Model.Forcing.Internal
open SetTheory SetTheory.Definitional.Project
universe u
variable {M : SetTheory.Structure.{u}} {B R z : M.Domain} {U : M.Domain → Prop}
variable (O : Cond_order_d M B R z) (hZF : M.Models ZF) (hU : Generic_d M B R z U)

local notation "E" => extension_l M hZF B R z U
include O hZF hU

theorem internal_pair_l (A C : (E).Domain) : ∃ Q : (E).Domain, ∀ x : (E).Domain,
    x ∈ Q ↔ x = A ∨ x = C := by
  obtain ⟨s, hs, hA⟩ := value_name_l A
  obtain ⟨t, ht, hC⟩ := value_name_l C
  obtain ⟨q, hq⟩ := npair_l M hZF B s t
  obtain ⟨Q, hQ⟩ := name_value_l (R := R) (z := z) (U := U) (npair_name_l M hZF hs ht hq)
  exact ⟨Q, npair_val_l O hZF hU hq hA hC hQ⟩

theorem internal_union_l (A : (E).Domain) : ∃ Q : (E).Domain, ∀ x : (E).Domain,
    x ∈ Q ↔ ∃ y : (E).Domain, y ∈ A ∧ x ∈ y := by
  obtain ⟨t, ht, hA⟩ := value_name_l A
  obtain ⟨S, htS, hS⟩ := ht
  let δ : Env M 2 := (⟨fun _ => t, fun _ => t⟩ : Env M 1).push R
  let φ : BinarySchema 2 := {
    body := .existsE (.conj (source_m (.bound 3) (.bound 4) .newest (.bound 1))
      (source_m (.bound 3) .newest (.bound 2) (.bound 1))) }
  have hφ s p : φ.denote δ s p ↔ ∃ a, Source_d M R t a p ∧ Source_d M R a s p := by
    simp only [BinarySchema.denote, φ, Formula.satisfies_exists_iff, Formula.satisfies_conj_iff,
      source_sat_l M hZF.1]
    rfl
  obtain ⟨q, hq, _, he⟩ := name_comp_l M hZF φ δ B S (fun a ha => ⟨S, ha, hS⟩)
  obtain ⟨Q, hQ⟩ := name_value_l (R := R) (z := z) (U := U) hq
  refine ⟨Q, fun x => ?_⟩
  constructor
  · intro hx
    obtain ⟨s, p, hs, hp, hsv⟩ := (qval_mem_l O hZF hU hQ).mp hx
    obtain ⟨a, ha, has⟩ := (hφ s p).mp ((he s p).mp hs).2.2
    have han : Name_d M B a := ha.elim fun c hc => (name_entry_l M ⟨S, htS, hS⟩ hc.1).1
    obtain ⟨y, hay⟩ := name_value_l (R := R) (z := z) (U := U) han
    exact ⟨y, source_val_l O hZF hU hA hay ha hp, source_val_l O hZF hU hay hsv has hp⟩
  · rintro ⟨y, hy, hx⟩
    obtain ⟨a, c, ha, hc, hav⟩ := (qval_mem_l O hZF hU hA).mp hy
    obtain ⟨s, d, hs, hd, hsv⟩ := (qval_mem_l O hZF hU hav).mp hx
    obtain ⟨p, hp, hpc, hpd⟩ := hU.directed c d hc hd
    have hsS := (supp_entry_l M hS (supp_entry_l M hS htS ha).1 hs).1
    exact (qval_mem_l O hZF hU hQ).mpr ⟨s, p, (he s p).mpr
      ⟨hsS, (hU.proper p hp).1, (hφ s p).mpr ⟨a, ⟨c, ha, hpc⟩, ⟨d, hs, hpd⟩⟩⟩, hp, hsv⟩

theorem check_val_mem_l {b a t} {x y : Name_quot_l M B R z U}
    (hc : Check_d M b a t) (hv : Qval_d M B R z U t x) (hb : U b) :
    y ∈ x ↔ ∃ c s, M.mem c a ∧ Check_d M b c s ∧ Qval_d M B R z U s y := by
  constructor
  · intro hy
    obtain ⟨s, p, hs, _, hsy⟩ := (qval_mem_l O hZF hU hv).mp hy
    obtain ⟨_, c, hca, hcs⟩ := (check_entry_l M hZF.1 (check_ind_l M hZF)
      (KP.exists_pair (ZF.modelsKP hZF)) hc s p).mp hs
    exact ⟨c, s, hca, hcs, hsy⟩
  · rintro ⟨c, s, hca, hcs, hsy⟩
    exact (qval_mem_l O hZF hU hv).mpr ⟨s, b, (check_entry_l M hZF.1 (check_ind_l M hZF)
      (KP.exists_pair (ZF.modelsKP hZF)) hc s b).mpr ⟨rfl, c, hca, hcs⟩, hb, hsy⟩

theorem internal_infinity_l : ∃ W : (E).Domain,
    (∃ e : (E).Domain, (∀ x : (E).Domain, ¬ x ∈ e) ∧ e ∈ W) ∧
    ∀ x : (E).Domain, x ∈ W → ∃ s : (E).Domain,
      (∀ y : (E).Domain, y ∈ s ↔ y ∈ x ∨ y = x) ∧ s ∈ W := by
  obtain ⟨b, hb⟩ := hU.inhabited
  have cv a : ∃ t, ∃ x : (E).Domain, Check_d M b a t ∧ Qval_d M B R z U t x := by
    obtain ⟨t, ht, hn, _⟩ := zf_check_l M hZF (hU.proper b hb).1 a
    obtain ⟨x, hx⟩ := name_value_l (R := R) (z := z) (U := U) hn
    exact ⟨t, x, ht, hx⟩
  obtain ⟨I, ⟨e, he, hei⟩, hI⟩ := KP.exists_inductive (ZF.modelsKP hZF)
  obtain ⟨tI, W, hcI, hvI⟩ := cv I
  obtain ⟨te, E', hce, hve⟩ := cv e
  refine ⟨W, ⟨E', fun x hx => ?_, ?_⟩, fun x hx => ?_⟩
  · obtain ⟨c, _, hc, _⟩ := (check_val_mem_l O hZF hU hce hve hb).mp hx
    exact he c hc
  · exact (check_val_mem_l O hZF hU hcI hvI hb).mpr ⟨e, te, hei, hce, hve⟩
  · obtain ⟨a, ta, hai, hca, hva⟩ := (check_val_mem_l O hZF hU hcI hvI hb).mp hx
    obtain ⟨s, hsa, hsi⟩ := hI a hai
    obtain ⟨ts, S, hcs, hvs⟩ := cv s
    refine ⟨S, fun y => ?_, (check_val_mem_l O hZF hU hcI hvI hb).mpr ⟨s, ts, hsi, hcs, hvs⟩⟩
    constructor
    · intro hy
      obtain ⟨c, tc, hct, hcc, hvc⟩ := (check_val_mem_l O hZF hU hcs hvs hb).mp hy
      rcases (hsa c).mp hct with hca' | hEq
      · exact Or.inl ((check_val_mem_l O hZF hU hca hva hb).mpr ⟨c, tc, hca', hcc, hvc⟩)
      · have heq := hZF.1.eq_of_same_members c a hEq
        subst c
        have ht := check_unique_l M hZF.1 (check_ind_l M hZF) b a tc ta hcc hca
        exact Or.inr (qval_unique_l (ht ▸ hvc) hva)
    · rintro (hy | rfl)
      · obtain ⟨c, tc, hca', hcc, hvc⟩ := (check_val_mem_l O hZF hU hca hva hb).mp hy
        exact (check_val_mem_l O hZF hU hcs hvs hb).mpr ⟨c, tc, (hsa c).mpr (Or.inl hca'), hcc, hvc⟩
      · exact (check_val_mem_l O hZF hU hcs hvs hb).mpr ⟨a, ta, hsa.predecessor_mem, hca, hva⟩

end YesMetaZFC.Model.Forcing.Internal

/-! ## 地模型内部名称扩张保持原 ZF

逐条核验仓库原公理及全分离、全收集模式。扩张域是内部名称模泛型等价的商，
外部非良基地模型使用同一接口；基础公理由模型内部归纳和泛型性证明。
-/

namespace YesMetaZFC.Model.Forcing.Internal
open SetTheory SetTheory.Definitional.Project
universe u
variable {M : SetTheory.Structure.{u}} {B R z : M.Domain} {U : M.Domain → Prop}
variable (O : Cond_order_d M B R z) (hZF : M.Models ZF) (hU : Generic_d M B R z U)
local notation "E" => extension_l M hZF B R z U
include O hZF hU

attribute [local simp] Formula.satisfies_mem_iff Formula.satisfies_neg_iff
  Formula.satisfies_conj_iff Formula.satisfies_disj_iff Formula.satisfies_imp_iff
  Formula.satisfies_iff_iff Formula.satisfies_forall_iff Formula.satisfies_exists_iff
  Formula.satisfies_subset_iff

/-- 给出原 ZF 模型性，包括任意有限参数的原分离、收集模式。 -/
theorem preserves_zf_l : (E).Models ZF := by
  refine ⟨extension_ext_l O hZF hU, fun s hs => ?_⟩
  cases hs with
  | extensionality =>
    rw [SetTheory.Structure.satisfiesSentence_iff]
    intro f
    simpa [Axioms.extensionality, Sentence.ofFormula,
      Formula.satisfies_extensionalEq_iff_eq (extension_ext_l O hZF hU)] using
      (extension_ext_l O hZF hU).eq_of_same_members
  | emptySet =>
    rw [SetTheory.Structure.satisfiesSentence_iff]
    intro f
    obtain ⟨e, he⟩ := KP.exists_empty (ZF.modelsKP hZF)
    obtain ⟨x, hx⟩ := name_value_l (R := R) (z := z) (U := U)
      (name_empty_l M (KP.exists_pair (ZF.modelsKP hZF)) B e he)
    have h : ∃ x : (E).Domain, ∀ y, ¬ (E).mem y x := ⟨x, fun y hy => by
      obtain ⟨s, b, ⟨p, _, hp⟩, _⟩ := (qval_mem_l O hZF hU hx).mp hy
      exact he p hp⟩
    simpa [Axioms.emptySet, Sentence.ofFormula] using h
  | foundation =>
    rw [SetTheory.Structure.satisfiesSentence_iff]
    intro f
    simpa [Axioms.foundation, Sentence.ofFormula] using internal_foundation_l O hZF hU
  | pairing =>
    rw [SetTheory.Structure.satisfiesSentence_iff]
    intro f
    simp only [Axioms.pairing, Sentence.ofFormula, Formula.satisfies_forall_iff,
      Formula.satisfies_exists_iff, Formula.satisfies_iff_iff, Formula.satisfies_disj_iff,
      Formula.satisfies_mem_iff, Formula.satisfies_extensionalEq_iff_eq (extension_ext_l O hZF hU),
      Definitional.Term.eval_newest, Definitional.Term.eval_weaken]
    simpa only [extension_l] using internal_pair_l O hZF hU
  | union =>
    rw [SetTheory.Structure.satisfiesSentence_iff]
    intro f
    simpa [Axioms.union, Sentence.ofFormula, extension_l] using internal_union_l O hZF hU
  | powerSet =>
    rw [SetTheory.Structure.satisfiesSentence_iff]
    intro f
    simpa [Axioms.powerSet, Sentence.ofFormula, extension_l] using internal_power_l O hZF hU
  | infinity =>
    rw [SetTheory.Structure.satisfiesSentence_iff]
    intro f
    simp only [Axioms.infinity, Sentence.ofFormula, Formula.satisfies_forall_iff, Formula.satisfies_forallMem_iff,
      Formula.satisfies_exists_iff, Formula.satisfies_conj_iff, Formula.satisfies_neg_iff,
      Formula.satisfies_iff_iff, Formula.satisfies_disj_iff,
      Formula.satisfies_mem_iff, Formula.satisfies_extensionalEq_iff_eq (extension_ext_l O hZF hU),
      Definitional.Term.eval_newest, Definitional.Term.eval_weaken]
    simpa only [extension_l] using internal_infinity_l O hZF hU
  | separation φ =>
    rw [SetTheory.Structure.satisfiesSentence_iff]
    intro f
    apply (Formula.satisfies_forallClosure_iff (ℳ := E) f (Axioms.Schema.separationCore φ)).mpr
    intro b
    apply (Axioms.Schema.separation_sat_iff_d _ φ).mpr
    simpa only [extension_l] using internal_separation_l O hZF hU φ (⟨b, f⟩ : Env E _)
  | collection φ =>
    rw [SetTheory.Structure.satisfiesSentence_iff]
    intro f
    apply (Formula.satisfies_forallClosure_iff (ℳ := E) f (Axioms.Schema.collectionCore φ)).mpr
    intro b
    apply (Axioms.Schema.collection_sat_iff_d _ φ).mpr
    simpa only [extension_l] using internal_collection_l O hZF hU φ (⟨b, f⟩ : Env E _)

end YesMetaZFC.Model.Forcing.Internal

/-! ## 反射后外部可数源的名字商仍可数

每个商值都有源模型内的名字代表，因此源载体的外部枚举给出商值的枚举。
此结果供反射中的泛型工厂使用，不断言模型内部 ω 标准或任意内部集合可数。
-/
namespace YesMetaZFC.Model.Forcing.Internal
open SetTheory
universe u
variable {M : Structure.{u}} (hZF : M.Models ZF)

theorem extension_countable_l {B R z : M.Domain} {G : M.Domain → Prop}
    (s : Nat → M.Domain) (onto : Function.Surjective s) :
    ∃ e : Nat → (extension_l M hZF B R z G).Domain, Function.Surjective e := by
  let E := extension_l M hZF B R z G
  have values n : ∃ y : E.Domain, Name_d M B (s n) → Qval_d M B R z G (s n) y := by
    rcases Classical.em (Name_d M B (s n)) with name | no
    · obtain ⟨y,value⟩ := name_value_l (R := R) (z := z) (U := G) name
      exact ⟨y,fun _ => value⟩
    · obtain ⟨y⟩ := E.nonempty
      exact ⟨y,fun h => (no h).elim⟩
  obtain ⟨e,read⟩ := Classical.axiomOfChoice values
  refine ⟨e,fun y => ?_⟩
  obtain ⟨τ,name,value⟩ := value_name_l y
  obtain ⟨n,rfl⟩ := onto τ
  exact ⟨n,qval_unique_l (read n name) value⟩

end YesMetaZFC.Model.Forcing.Internal

/-! ## 内部名称扩张保持选择公理

在地模型中枚举源名称的闭支撑，把每个非空集合的最早隶属候选收集成加权名称。
稠密性保证每个族成员获得选值，最小指标唯一性保证选择不依赖名称呈现。
最终直接给出仓库原 ZFC 模型接口。
-/

namespace YesMetaZFC.Model.Forcing.Internal
open SetTheory SetTheory.Definitional.Project
universe u
variable {M : SetTheory.Structure.{u}} {B R z : M.Domain} {U : M.Domain → Prop}
variable (O : Cond_order_d M B R z) (h : M.Models ZFC) (hU : Generic_d M B R z U)

local notation "E" => extension_l M (ZFC.models_zf_l h) B R z U
include O h hU

theorem internal_choice_l (A : (E).Domain)
    (hn : ∀ a : (E).Domain, a ∈ A → ∃ x : (E).Domain, x ∈ a)
    (hd : ∀ a : (E).Domain, a ∈ A → ∀ b : (E).Domain, b ∈ A →
      a ≠ b → ¬ ∃ x : (E).Domain, x ∈ a ∧ x ∈ b) :
    ∃ C : (E).Domain, ∀ a : (E).Domain, a ∈ A →
      ∃ x : (E).Domain, (x ∈ C ∧ x ∈ a) ∧
        ∀ y : (E).Domain, (y ∈ C ∧ y ∈ a) → y = x := by
  let hZF := ZFC.models_zf_l h
  let I := kpair_interpretation_l M hZF.1 (KP.exists_pair (ZF.modelsKP hZF))
  obtain ⟨τ, ⟨S, hτS, hS⟩, hA⟩ := value_name_l A
  obtain ⟨κ, F, hκ, hf, hsur⟩ := ZFC.ordinal_enum_l h I S
  let δ : Env M 6 := (((((⟨fun _ => B, fun _ => B⟩ : Env M 1).push R).push z).push F).push κ).push τ
  let φ : BinarySchema 6 := {
    body := .existsE (.conj (source_m (.bound 7) (.bound 3) .newest (.bound 1))
      (min_mem_m (.bound 8) (.bound 7) (.bound 6) (.bound 5) (.bound 4) (.bound 1) (.bound 2) .newest)) }
  have hφ s p : φ.denote δ s p ↔ ∃ t, Source_d M R τ t p ∧ Min_mem_d M B R z F κ p s t := by
    simp only [BinarySchema.denote, φ, Formula.satisfies_exists_iff, Formula.satisfies_conj_iff,
      source_sat_l M hZF.1, min_mem_sat_l M hZF.1]
    rfl
  obtain ⟨c, hc, _, he⟩ := name_comp_l M hZF φ δ B S (fun s hs => ⟨S, hs, hS⟩)
  obtain ⟨C, hC⟩ := name_value_l (R := R) (z := z) (U := U) hc
  refine ⟨C, fun a ha => ?_⟩
  obtain ⟨t, b, ht, hb, hta⟩ := (qval_mem_l O hZF hU hA).mp ha
  obtain ⟨y, hy⟩ := hn a ha
  obtain ⟨s, d, hs, _, hsy⟩ := (qval_mem_l O hZF hU hta).mp hy
  have htS := (supp_entry_l M hS hτS ht).1
  have hsS := (supp_entry_l M hS htS hs).1
  obtain ⟨i, hi, his⟩ := hsur s hsS
  obtain ⟨q, hq, hm⟩ := (qval_mem_forcing_l O hZF hU hsy hta).mpr hy
  obtain ⟨p, hp, s, hm⟩ := generic_pick_l hZF hU (min_mem_defined_l M hZF.1 B R z F κ t) hq
    (min_mem_dense_l O hZF hκ hi his hm)
  have hsS : M.mem s S := hf.output_mem_of_pairMember hm.choose_spec.2.1
  obtain ⟨x, hsx⟩ := name_value_l (R := R) (z := z) (U := U) (⟨S, hsS, hS⟩ : Name_d M B s)
  obtain ⟨r, hr, hrp, hrb⟩ := hU.directed p b hp hb
  have hr' := hU.proper r hr
  have hmr := min_mem_lower_l O F κ s t p r (hU.proper p hp).1 ⟨hr'.1, hr'.2, hrp⟩ hm
  have hxC := (qval_mem_l O hZF hU hC).mpr ⟨s, r, (he s r).mpr
    ⟨hsS, hr'.1, (hφ s r).mpr ⟨t, ⟨b, ht, hrb⟩, hmr⟩⟩, hr, hsx⟩
  have hxa := (qval_mem_forcing_l O hZF hU hsx hta).mp ⟨r, hr, hmr.choose_spec.2.2.1⟩
  refine ⟨x, ⟨hxC, hxa⟩, fun y ⟨hyC, hya⟩ => ?_⟩
  obtain ⟨v, q, hv, hq, hvy⟩ := (qval_mem_l O hZF hU hC).mp hyC
  obtain ⟨w, hw, hmw⟩ := (hφ v q).mp ((he v q).mp hv).2.2
  have hwN : Name_d M B w := hw.elim fun d hd => (name_entry_l M ⟨S, hτS, hS⟩ hd.1).1
  obtain ⟨a', hwa⟩ := name_value_l (R := R) (z := z) (U := U) hwN
  have ha'A := source_val_l O hZF hU hA hwa hw hq
  have hya' := (qval_mem_forcing_l O hZF hU hvy hwa).mp ⟨q, hq, hmw.choose_spec.2.2.1⟩
  have haa : a' = a := by
    apply Classical.byContradiction
    intro hn
    exact hd a' ha'A a ha hn ⟨y, hya', hya⟩
  subst a'
  exact min_mem_unique_l O hZF hU hκ hf hq hr hvy hsx hwa hta hmw hmr

theorem internal_choice_axiom_l : (E).SatisfiesSentence Axioms.choice := by
  rw [SetTheory.Structure.satisfiesSentence_iff]
  intro f
  simp only [Axioms.choice, Sentence.ofFormula, Formula.satisfies_forall_iff,
    Formula.satisfies_forallMem_iff, Formula.satisfies_exists_iff, Formula.satisfies_imp_iff,
    Formula.satisfies_conj_iff, Formula.extensionalNe, Formula.satisfies_neg_iff,
    Formula.satisfies_mem_iff, Formula.satisfies_extensionalEq_iff_eq (extension_ext_l O (ZFC.models_zf_l h) hU),
    Definitional.Term.eval_newest, Definitional.Term.eval_weaken]
  intro A ⟨hn, hd⟩
  exact internal_choice_l O h hU A hn hd

/-- 一次调用获得内部泛型扩张的全部原 ZFC 公理与模式；名称域非空性自动构造。 -/
theorem preserves_zfc_l : (extension_l M (ZFC.models_zf_l h) B R z U).Models ZFC := by
  have hE := preserves_zf_l O (ZFC.models_zf_l h) hU
  refine ⟨hE.1, fun s hs => ?_⟩
  cases hs with
  | zf hs => exact hE.2 s hs
  | choice => exact internal_choice_axiom_l O h hU

omit O h hU in
/-- 实际小图地模型和二元布尔主泛型滤子，直接实例化完整 ZFC 保持端点。 -/
theorem two_extension_zfc_l :
    (extension_l SmallGraph.sg_structure (ZFC.models_zf_l SmallGraph.sg_project_zfc)
      two_conditions_l two_relation_l two_zero_l two_filter_l).Models ZFC :=
  preserves_zfc_l two_cond_order_l SmallGraph.sg_project_zfc two_generic_l

end YesMetaZFC.Model.Forcing.Internal
