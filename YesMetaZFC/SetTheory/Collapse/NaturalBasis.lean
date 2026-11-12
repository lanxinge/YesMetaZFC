import YesMetaZFC.SetTheory.Collapse.PairReflection
import YesMetaZFC.SetTheory.KP.Natural

/-! # 由常零与后继实数回收全部自然数

两张特殊实数图都在 KP 中实际构造。若满坍塌把它们仍解释为背景 ω 上的
常零与后继图，则原载体包含全部背景自然数，且逐点固定它们。
归纳性质为有界图公式，不把外部标准自然数归纳代入内部 ω。
-/
namespace YesMetaZFC.SetTheory
open Definitional.Project InnerModel
universe u
variable {M : Structure.{u}}

structure Mc_nat_d (ω z c s : M.Domain) : Prop where
  omega : M.IsOmega ω
  empty : ∀ x, ¬ M.mem x z
  constant : Fn0_d ω ω c
  constant_entry : ∀ n y, Rd_entry_d n y c ↔ M.mem n ω ∧ y = z
  successor : Fn0_d ω ω s
  successor_entry : ∀ n y, Rd_entry_d n y s ↔ M.mem n ω ∧ M.SuccessorOf y n

def mc_nat_m {n} (ω z c s : Term n) : Formula 1 n := set[n] ⟪
  ⌜Formula.isOmega⌝ₚ(⌜ω⌝ₛ) ∧ ⌜Formula.isEmpty⌝ₚ(⌜z⌝ₛ) ∧
  ⌜fn0_m⌝ₚ(⌜ω⌝ₛ,⌜ω⌝ₛ,⌜c⌝ₛ) ∧
  (∀ i, ∀ y, (⌜rd_entry0_m⌝ₚ(i,y,⌜c⌝ₛ) ↔ i ∈ ⌜ω⌝ₛ ∧ y = ⌜z⌝ₛ)) ∧
  ⌜fn0_m⌝ₚ(⌜ω⌝ₛ,⌜ω⌝ₛ,⌜s⌝ₛ) ∧
  (∀ i, ∀ y, (⌜rd_entry0_m⌝ₚ(i,y,⌜s⌝ₛ) ↔ i ∈ ⌜ω⌝ₛ ∧ ⌜KP.succ0_m⌝ₚ(y,i)))⟫
derive_free_closed mc_nat_m

theorem mc_nat_sat_l (hE : Extensional M) {n} (ρ : Env M n) (ω z c s : Term n) :
    Formula.satisfies ρ (mc_nat_m ω z c s) ↔ Mc_nat_d (ω.eval ρ) (z.eval ρ) (c.eval ρ) (s.eval ρ) := by
  simp only [mc_nat_m,Formula.satisfies_conj_iff,Formula.satisfies_isOmega_iff,Formula.satisfies_isEmpty_iff,
    fn0_sat_l hE,Formula.satisfies_forall_iff,Formula.satisfies_iff_iff,rd_entry0_sat_l hE,
    Formula.satisfies_mem_iff,Formula.satisfies_extensionalEq_iff_eq hE,KP.succ0_sat_l hE,
    Definitional.Term.eval_weaken]
  exact ⟨fun h => ⟨h.1,h.2.1,h.2.2.1,h.2.2.2.1,h.2.2.2.2.1,h.2.2.2.2.2⟩,
    fun h => ⟨h.omega,h.empty,h.constant,h.constant_entry,h.successor,h.successor_entry⟩⟩

theorem mc_nat_exists_l (hKP : M.Models KP) {ω : M.Domain} (hω : M.IsOmega ω) :
    ∃ z c s, Mc_nat_d ω z c s := by
  obtain ⟨z,hz,hzω⟩ := hω.1.1
  let δ : Delta0BinarySchema 1 := { body := Formula.extensionalEq .newest (.bound 2), delta0 := .atom _ _ _ }
  let ρ : Env M 1 := ⟨fun _ => z,fun _ => z⟩
  have zero n y : (S1_binary.of_delta0 δ).schema.denote ρ n y ↔ y = z :=
    (S1_binary.of_delta0_sat_l ..).trans (Formula.satisfies_extensionalEq_iff_eq hKP.1 ..)
  obtain ⟨c,hc,ec⟩ := s1_function_l hKP (.of_delta0 δ) ρ ω ω
    (fun n _ => ⟨z,(zero n z).mpr rfl⟩)
    (fun n _ a b ha hb => ((zero n a).mp ha).trans ((zero n b).mp hb).symm)
    (fun n _ y hy => ((zero n y).mp hy).symm ▸ hzω)
  let ε : Delta0BinarySchema 0 := { body := KP.succ0_m .newest (.bound 1), delta0 := KP.succ0_delta_l .. }
  let η : Env M 0 := ⟨Fin.elim0,fun _ => z⟩
  have succ n y : (S1_binary.of_delta0 ε).schema.denote η n y ↔ M.SuccessorOf y n :=
    (S1_binary.of_delta0_sat_l ..).trans (KP.succ0_sat_l hKP.1 ..)
  obtain ⟨s,hs,es⟩ := s1_function_l hKP (.of_delta0 ε) η ω ω
    (fun n hn => (hω.1.2 n hn).imp fun y hy => (succ n y).mpr hy.1)
    (fun n _ a b ha hb => Structure.SuccessorOf.eq hKP.1 ((succ n a).mp ha) ((succ n b).mp hb))
    (fun n hn y hy => by
      obtain ⟨v,hv,hvω⟩ := hω.1.2 n hn
      exact Structure.SuccessorOf.eq hKP.1 hv ((succ n y).mp hy) ▸ hvω)
  exact ⟨z,c,s,hω,hz,hc,fun n y => (ec n y).trans (and_congr_right fun _ => zero n y),
    hs,fun n y => (es n y).trans (and_congr_right fun _ => succ n y)⟩

/-- 满成员映射在源序数上已单射，不要求它在整个载体上单射。 -/
theorem Mc_map_d.ordinal_injective_l (hKP : M.Models KP) {Q B F a b y : M.Domain}
    (h : Mc_map_d Q B F) (ha : M.IsOrdinal a) (hb : M.IsOrdinal b)
    (ea : Rd_entry_d a y F) (eb : Rd_entry_d b y F) : a = b := by
  rcases ha.trichotomy hKP.1 hb (KP.difference_exists_d hKP) (KP.intersection_exists_d hKP a b) with eq | lt | gt
  · exact hKP.1.eq_of_same_members a b eq
  · exact (KP.mem_irrefl_d hKP y ((h.member a b y y ea eb).mp lt)).elim
  · exact (KP.mem_irrefl_d hKP y ((h.member b a y y eb ea).mp gt)).elim

/-- 像图只需包含正确的常零边与后继边，便强制自然数支撑完整。 -/
theorem Mc_map_d.naturals_l (hKP : M.Models KP) {Q B F ω z c s C S : M.Domain}
    (h : Mc_map_d Q B F) (ht : M.TransitiveSet B)
    (basis : Mc_nat_d ω z c s) (ec : Rd_entry_d c C F) (es : Rd_entry_d s S F)
    (hc : ∀ n, M.mem n ω → Rd_entry_d n z C)
    (hs : ∀ n, M.mem n ω → ∀ v, M.SuccessorOf v n → Rd_entry_d n v S) :
    M.MemberSubset ω Q ∧ ∀ n, M.mem n ω → Rd_entry_d n n F := by
  have hω := basis.omega
  have lift {r R i j : M.Domain} (fr : Fn0_d ω ω r) (er : Rd_entry_d r R F)
      (ij : Rd_entry_d i j R) (ne : i ≠ j) :
      ∃ n m, Rd_entry_d n m r ∧ Rd_entry_d n i F ∧ Rd_entry_d m j F := by
    obtain ⟨q,pair,hq⟩ := ij
    obtain ⟨p,ep⟩ := h.onto q (ht R (h.function.bound_l er).2 q hq)
    have hp := (h.member p r q R ep er).mpr hq
    obtain ⟨n,_,m,_,original⟩ := fr.1 p hp
    obtain ⟨_,_,en,em⟩ := h.kpair_preimage_l ht original pair ep ne
    exact ⟨n,m,⟨p,original,hp⟩,en,em⟩
  have zero : Rd_entry_d z z F := by
    obtain ⟨e,he,heω⟩ := hω.1.1
    have ez : e = z := hKP.1.eq_of_same_members e z (fun a => iff_of_false (he a) (basis.empty a))
    subst e
    obtain ⟨one,ho,hoω⟩ := hω.1.2 z heω
    have ne : one ≠ z := fun eq => basis.empty z (eq ▸ ho.predecessor_mem)
    obtain ⟨n,m,nm,_,em⟩ := lift basis.constant ec (hc one hoω) ne
    exact ((basis.constant_entry n m).mp nm).2 ▸ em
  let ρ : Env M 1 := ⟨fun _ => F,fun _ => F⟩
  let φ : Delta0UnarySchema 1 := { body := rd_entry0_m .newest .newest (.bound 1), delta0 := rd_entry0_delta_l .. }
  have sat n : φ.toUnarySchema.denote ρ n ↔ Rd_entry_d n n F := rd_entry0_sat_l hKP.1 ..
  obtain ⟨D,hd⟩ := KP.separation_exists_d hKP φ ρ ω
  have all : ∀ n, M.mem n ω → Rd_entry_d n n F := hω.induction _
    ⟨D,fun n => (hd n).trans (and_congr_right fun _ => sat n)⟩
    (fun e he => by
      have eq := hKP.1.eq_of_same_members e z (fun a => iff_of_false (he a) (basis.empty a))
      exact eq.symm ▸ zero)
    (fun n hn en v hv => by
      have ne : n ≠ v := fun eq => KP.mem_irrefl_d hKP v (eq ▸ hv.predecessor_mem)
      obtain ⟨k,l,kl,ek,el⟩ := lift basis.successor es (hs n hn v hv) ne
      have hk := (basis.successor.bound_l kl).1
      have eq := h.ordinal_injective_l hKP (hω.members_areOrdinals hKP k hk) (hω.members_areOrdinals hKP n hn) ek en
      subst k
      have ev := Structure.SuccessorOf.eq hKP.1 ((basis.successor_entry n l).mp kl).2 hv
      exact ev ▸ el)
  exact ⟨fun n hn => (h.function.bound_l (all n hn)).1,all⟩

end YesMetaZFC.SetTheory
