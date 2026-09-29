import YesMetaZFC.Model.Forcing.InternalNameConstruction

/-! # 幂集保持：将扩张子集正规化为地模型有界名称

源名称的闭支撑 S 给出内部界 S×B。扩张中的每个子集都可用这个界的一个内部
子集名称表示；模型的幂集公理因此足以收集全部扩张子集，不取宿主的全幂集。
-/

namespace YesMetaZFC.Model.Forcing.Internal
open SetTheory SetTheory.Definitional.Project SmallGraph
universe u v
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

theorem sub_name_val_l {B R} {U : M.Domain → Prop}
    (hu : ∀ p q, U p → M.mem q B → Entry_d M p q R → U q)
    {s t} {x y : SG_set.{v}} (hs : Val_d M B U s x) (ht : Val_d M B U t y)
    (h : Sub_name_d M R t s) : ∀ w, w ∈ x → w ∈ y := by
  intro w hw
  obtain ⟨a, b, ha, hb, hv⟩ := (val_mem_l M hs).mp hw
  exact source_val_l M hu ht hv (h a b ha) hb

variable {M} {B R z : M.Domain} {U : M.Domain → Prop}
  (O : Cond_order_d M B R z) (hZF : M.Models ZF) (hU : Generic_d M B R z U)
  (hM : _root_.WellFounded M.mem) (hL : Setlike_d.{u, v} M)
include O hZF hU hM hL

/-- 子集名称只使用原支撑中的子名称；每个系数加强某个原成员系数。 -/
theorem normalize_name_l {S s t} (hS : Supp_d M B S) (htS : M.mem t S)
    {x y : SG_set.{v}} (hs : Val_d M B U s x) (ht : Val_d M B U t y)
    (hxy : ∀ w, w ∈ x → w ∈ y) :
    ∃ q, Name_d M B q ∧
      (∀ p, M.mem p q → ∃ a b, M.mem a S ∧ M.mem b B ∧ KPair_d M p a b) ∧
      Sub_name_d M R t q ∧ Val_d M B U q x := by
  let δ : Env M 5 := ((((⟨fun _ => B, fun _ => B⟩ : Env M 1).push R).push z).push t).push s
  let φ : BinarySchema 5 := {
    body := .conj (source_m (.bound 5) (.bound 3) (.bound 1) (.bound 0))
      (mem_force_m (.bound 6) (.bound 5) (.bound 4) (.bound 0) (.bound 1) (.bound 2)) }
  have hφ a b : φ.denote δ a b ↔ Source_d M R t a b ∧ Mem_force_d M B R z b a s := by
    simp only [BinarySchema.denote, φ, Formula.satisfies_conj_iff, source_sat_l M hZF.1,
      mem_force_sat_l M hZF.1]
    rfl
  obtain ⟨q, hq, hqmem, he⟩ := name_comp_l M hZF φ δ B S (fun a ha => ⟨S, ha, hS⟩)
  obtain ⟨w, hw, _⟩ := val_exists_unique_l M hM hL B U hq
  have hwx : w = x := by
    apply SG_set.ext
    intro a
    constructor
    · intro ha
      obtain ⟨b, p, hb, hp, hbv⟩ := (val_mem_l M hw).mp ha
      exact (val_mem_forcing_l O hZF hU hbv hs).mp ⟨p, hp, ((hφ b p).mp ((he b p).mp hb).2.2).2⟩
    · intro ha
      obtain ⟨b, c, hb, hc, hbv⟩ := (val_mem_l M ht).mp (hxy a ha)
      obtain ⟨p, hp, hmem⟩ := (val_mem_forcing_l O hZF hU hbv hs).mpr ha
      obtain ⟨d, hd, hdc, hdp⟩ := hU.directed c p hc hp
      have hd' := hU.proper d hd
      have hmem' := (regular_mem_l O b s).1 p d (hU.proper p hp).1 ⟨hd'.1, hd'.2, hdp⟩ hmem
      exact (val_mem_l M hw).mpr ⟨b, d, (he b d).mpr
        ⟨(supp_entry_l M hS htS hb).1, hd'.1, (hφ b d).mpr ⟨⟨c, hb, hdc⟩, hmem'⟩⟩, hd, hbv⟩
  refine ⟨q, hq, ?_, ?_, hwx ▸ hw⟩
  · intro p hp
    obtain ⟨a, b, ha, hb, h, _⟩ := (hqmem p).mp hp
    exact ⟨a, b, ha, hb, h⟩
  · exact fun a b h => ((hφ a b).mp ((he a b).mp h).2.2).1

variable (hN : ∃ t, Name_d M B t)
local notation "E" => ext_structure_l (name_domain_l M hM hL B hN) U

theorem internal_power_l (A : (E).Domain) : ∃ P : (E).Domain, ∀ X : (E).Domain,
    X.1 ∈ P.1 ↔ ∀ Y : (E).Domain, Y.1 ∈ X.1 → Y.1 ∈ A.1 := by
  obtain ⟨t, ht, hA⟩ := value_name_l hM hL hN A
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
  obtain ⟨P, hP⟩ := name_value_l hM hL hN hq
  refine ⟨P, fun X => ?_⟩
  constructor
  · intro hX Y hY
    obtain ⟨s, p, hs, _, hsv⟩ := (val_mem_l M hP).mp hX
    exact sub_name_val_l M hU.upward hsv hA ((hφ s p).mp ((he s p).mp hs).2.2).2 Y.1 hY
  · intro hX
    obtain ⟨s, _, hsv⟩ := value_name_l hM hL hN X
    have hsub w (hw : w ∈ X.1) : w ∈ A.1 :=
      hX ⟨w, ext_transitive_l _ U X.2 hw⟩ hw
    obtain ⟨s', _, hs', hst, hv⟩ := normalize_name_l O hZF hU hM hL hS htS hsv hA hsub
    have hsK : M.mem s' K := (hK s').mpr (fun p hp => by
      obtain ⟨a, c, ha, hc, h⟩ := hs' p hp
      exact (hT p).mpr ⟨a, ha, c, hc, h⟩)
    exact (val_mem_l M hP).mpr ⟨s', b, (he s' b).mpr
      ⟨hsK, (hU.proper b hb).1, (hφ s' b).mpr ⟨rfl, hst⟩⟩, hb, hv⟩

end YesMetaZFC.Model.Forcing.Internal
