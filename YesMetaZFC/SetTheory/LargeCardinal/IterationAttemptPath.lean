import YesMetaZFC.SetTheory.LargeCardinal.IterationAttemptSpace
import YesMetaZFC.SetTheory.LargeCardinal.IterationBranch
import YesMetaZFC.SetTheory.RelationChain
import YesMetaZFC.SetTheory.Card.Omega

/-! # 内部无限尝试链确定共尾树枝

沿内部 ω 链的末结点严格递增；若有有限上界，就得到 ω 到有限序数的单射。
末结点的全部前驱取并即为共尾枝，而且每个枝结点的行达到任意有限长度。
-/
namespace YesMetaZFC.SetTheory.LargeCardinal
open Definitional.Project InnerModel Internal
universe u
variable {M : Structure.{u}}

def Ja_seen_d (T g i : M.Domain) : Prop := ∃ n s k P,
  Rd_entry_d n s g ∧ KPair_d M s k P ∧ Rd_entry_d i k T

def ja_seen_m {d} (T g i : Term d) : Formula 1 d := set[d] ⟪
  ∃ n s k P, ⌜rd_entry0_m⌝ₚ(n, s, ⌜g⌝ₛ) ∧ ⌜kpair_m⌝ₚ(s, k, P) ∧ ⌜rd_entry0_m⌝ₚ(⌜i⌝ₛ, k, ⌜T⌝ₛ)⟫
derive_free_closed ja_seen_m

theorem ja_seen_sat_l (hE : Extensional M) {d} (ρ : Env M d) (T g i : Term d) :
    Formula.satisfies ρ (ja_seen_m T g i) ↔ Ja_seen_d (T.eval ρ) (g.eval ρ) (i.eval ρ) := by
  simp only [ja_seen_m, Ja_seen_d, Formula.satisfies_exists_iff, Formula.satisfies_conj_iff,
    rd_entry0_sat_l hE, kpair_sat_l M hE, Definitional.Term.eval_weaken]; rfl

structure Ja_path_d (ω T g B : M.Domain) : Prop where
  branch : It_branch_d ω T B
  seen : ∀ i, M.mem i B ↔ Ja_seen_d T g i
  chain : ∀ n m s t, M.mem n m → Rd_entry_d n s g → Rd_entry_d m t g → Ja_extend_d T s t
  wide : ∀ i n, M.mem i B → M.mem n ω → ∃ m s k P,
    Rd_entry_d m s g ∧ KPair_d M s k P ∧ Rd_entry_d i k T ∧ M.mem n k

variable (hZF : M.Models ZF)
local notation "I" => kp_pair_l (ZF.modelsKP hZF)

theorem ja_path_l {ω T Q G E Y W z π A R g : M.Domain} (hω : M.IsOmega ω)
    (h : It_order_d ω T) (space : Ja_space_d I ω T Q G E Y W z π A R)
    (fg : Fn0_d ω A g) (desc : Wf_desc_d R g) : ∃ B, Ja_path_d ω T g B := by
  have gf := fn0_function_l (ZF.modelsKP hZF) fg
  let φ : BinarySchema 1 := { body := ja_extend_m (.bound 2) (.bound 1) .newest }
  let η : Env M 1 := ⟨fun _ => T, fun _ => T⟩
  have sat s t : φ.denote η s t ↔ Ja_extend_d T s t := ja_extend_sat_l hZF.1 ..
  have chain n m s t (hnm : M.mem n m) (hs : Rd_entry_d n s g) (ht : Rd_entry_d m t g) : Ja_extend_d T s t :=
    (sat s t).mp (ZF.rel_chain_l I hZF φ η hω gf
      (fun s t u hs ht hu st tu => (sat s u).mpr (ja_extend_trans_l hZF h
        ((space.nodes s).mp hs) ((space.nodes t).mp ht) ((space.nodes u).mp hu) ((sat s t).mp st) ((sat t u).mp tu)))
      (fun n m s t hm hs ht => (sat s t).mpr ((space.edges s t).mp (desc n m s t hm hs ht)).2.2) n m s t hnm hs ht)
  let ψ : BinarySchema 1 := { body := .existsE (.existsE (.conj
    (rd_entry0_m (.bound 3) (.bound 1) (.bound 4)) (kpair_m (.bound 1) (.bound 2) .newest))) }
  let ρ : Env M 1 := ⟨fun _ => g, fun _ => g⟩
  have psat n k : ψ.denote ρ n k ↔ ∃ s P, Rd_entry_d n s g ∧ KPair_d M s k P := by
    simp only [ψ, BinarySchema.denote, Formula.satisfies_exists_iff, Formula.satisfies_conj_iff,
      rd_entry0_sat_l hZF.1, kpair_sat_l M hZF.1]; rfl
  obtain ⟨f, ff, fs⟩ := ZF.exists_setFunctionFromTo_of_denote hZF I ψ ρ (source := ω) (target := ω)
    (fun n hn => by
      obtain ⟨s, hs, hns⟩ := fg.2.1 n hn
      obtain ⟨k, P, hp, _⟩ := (space.nodes s).mp hs
      exact ⟨k, (psat n k).mpr ⟨s, P, hns, hp⟩⟩)
    (fun n _ k l hk hl => by
      obtain ⟨s, P, hs, hp⟩ := (psat n k).mp hk
      obtain ⟨t, Q', ht, hq⟩ := (psat n l).mp hl
      exact (kpair_injective_l M ((gf.1.2 n s t hs ht) ▸ hp) hq).1)
    (fun n k _ hk => by
      obtain ⟨s, P, hs, hp⟩ := (psat n k).mp hk
      obtain ⟨l, Q', hq, node⟩ := (space.nodes s).mp (fg.bound_l hs).2
      exact (kpair_injective_l M hq hp).1 ▸ node.length)
  have point n k (hk : Rd_entry_d n k f) := (psat n k).mp ((fs n k).mp hk).2
  have inc n m k l (hnm : M.mem n m) (hk : Rd_entry_d n k f) (hl : Rd_entry_d m l f) : M.mem k l := by
    obtain ⟨s, P, hs, hp⟩ := point n k hk
    obtain ⟨t, Q', ht, hq⟩ := point m l hl
    exact ((chain n m s t hnm hs ht).read_l hp hq).1
  have inject : M.IsSetInjective I f := by
    intro n m k hn hm
    rcases h.ordinal.wellOrder.linear.compare n (ff.input_mem_of_pairMember hn) m (ff.input_mem_of_pairMember hm) with eq | hnm | hmn
    · exact hZF.1.eq_of_same_members n m eq
    · exact (KP.mem_irrefl_d (ZF.modelsKP hZF) k (inc n m k k hnm hn hm)).elim
    · exact (KP.mem_irrefl_d (ZF.modelsKP hZF) k (inc m n k k hmn hm hn)).elim
  have cofinal i (hi : M.mem i ω) : ∃ n k, Rd_entry_d n k f ∧ M.mem i k := by
    apply Classical.byContradiction
    intro no
    obtain ⟨l, hl, hlω⟩ := hω.1.2 i hi
    have bound n k (hk : Rd_entry_d n k f) : M.mem k l := by
      rcases h.ordinal.wellOrder.linear.compare k (ff.output_mem_of_pairMember hk) i hi with eq | hki | hik
      · exact hZF.1.eq_of_same_members k i eq ▸ hl.predecessor_mem
      · exact (hl k).mpr (Or.inl hki)
      · exact (no ⟨n, k, hk, hik⟩).elim
    exact ZF.omega_not_le_finite_l I hZF hω l hlω
      ⟨f, fn0_function_l (ZF.modelsKP hZF) ((fn0_of_function_l (ZF.modelsKP hZF) ff).retarget_l bound), inject⟩
  let χ : UnarySchema 2 := { body := ja_seen_m (.bound 1) (.bound 2) .newest }
  obtain ⟨B, bs⟩ := ZF.separation_exists_d hZF χ ⟨Fin.cases T (fun _ => g), fun _ => g⟩ ω
  have seen i : M.mem i B ↔ Ja_seen_d T g i := by
    have read : M.mem i B ↔ M.mem i ω ∧ Ja_seen_d T g i := by
      simpa only [χ, UnarySchema.denote, ja_seen_sat_l hZF.1] using! bs i
    exact read.trans ⟨And.right, fun ⟨n, s, k, P, hs, hp, hik⟩ =>
      ⟨(h.bound i k hik).1, n, s, k, P, hs, hp, hik⟩⟩
  have compare i j (hi : M.mem i B) (hj : M.mem j B) : Rd_entry_d i j T ∨ Rd_entry_d j i T := by
    obtain ⟨n, s, k, P, hs, hp, hik⟩ := (seen i).mp hi
    obtain ⟨m, t, l, Q', ht, hq, hjl⟩ := (seen j).mp hj
    rcases h.ordinal.wellOrder.linear.compare n (fg.bound_l hs).1 m (fg.bound_l ht).1 with eq | hnm | hmn
    · have eq := hZF.1.eq_of_same_members n m eq
      subst m
      have eq := (kpair_injective_l M ((gf.1.2 n s t hs ht) ▸ hp) hq).1
      exact h.chain i j l (eq ▸ hik) hjl
    · exact h.chain i j l (h.trans i k l hik ((chain n m s t hnm hs ht).read_l hp hq).2.1) hjl
    · exact h.chain i j k hik (h.trans j l k hjl ((chain m n t s hmn ht hs).read_l hq hp).2.1)
  have branch : It_branch_d ω T B := ⟨fun i hi => by
      obtain ⟨_, _, k, _, _, _, hik⟩ := (seen i).mp hi
      exact (h.bound i k hik).1, compare, fun i j hij hj => by
      obtain ⟨n, s, k, P, hs, hp, hjk⟩ := (seen j).mp hj
      exact (seen i).mpr ⟨n, s, k, P, hs, hp, h.trans i j k hij hjk⟩, fun i hi => by
      obtain ⟨n, k, hk, hik⟩ := cofinal i hi
      obtain ⟨s, P, hs, hp⟩ := point n k hk
      exact ⟨k, (seen k).mpr ⟨n, s, k, P, hs, hp, h.refl k (ff.output_mem_of_pairMember hk)⟩, Or.inr hik⟩⟩
  refine ⟨B, branch, seen, chain, fun i a hi ha => ?_⟩
  obtain ⟨n, s, k, P, hs, hp, hik⟩ := (seen i).mp hi
  obtain ⟨m, l, hl, hal⟩ := cofinal a ha
  obtain ⟨t, Q', ht, hq⟩ := point m l hl
  rcases h.ordinal.wellOrder.linear.compare n (fg.bound_l hs).1 m (fg.bound_l ht).1 with eq | hnm | hmn
  · have eq := hZF.1.eq_of_same_members n m eq
    subst m
    have eq := (kpair_injective_l M ((gf.1.2 n s t hs ht) ▸ hp) hq).1
    exact ⟨n, t, l, Q', ht, hq, eq ▸ hik, hal⟩
  · exact ⟨m, t, l, Q', ht, hq, h.trans i k l hik ((chain n m s t hnm hs ht).read_l hp hq).2.1, hal⟩
  · have lk := ((chain m n t s hmn ht hs).read_l hq hp).1
    exact ⟨n, s, k, P, hs, hp, hik, (h.ordinal.mem (h.bound i k hik).2).transitive l lk a hal⟩

end YesMetaZFC.SetTheory.LargeCardinal
