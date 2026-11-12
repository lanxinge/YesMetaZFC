import YesMetaZFC.SetTheory.LargeCardinal.Iteration.AttemptMember
import YesMetaZFC.SetTheory.LargeCardinal.Iteration.Branch
import YesMetaZFC.SetTheory.RelationChain
import YesMetaZFC.SetTheory.Card.Omega
import YesMetaZFC.SetTheory.OrdinalChoice
import YesMetaZFC.SetTheory.LargeCardinal.Iteration.BranchTail
import YesMetaZFC.SetTheory.LargeCardinal.Iteration.ReturnFactor
import YesMetaZFC.SetTheory.Collapse.RelationRank

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

/-! ## 联合枝各行解码为完整初等嵌入

先并合一行的全部有限记录，再取枚举的最小编号截面并复合。
同一公式给出唯一图，因此随后可收集整列嵌入，无须选择它们。
-/
namespace YesMetaZFC.SetTheory.LargeCardinal
open Definitional.Project InnerModel Internal
universe u
variable {M : Structure.{u}}

def Ja_observe_d (g i a y : M.Domain) : Prop := ∃ n s k P p,
  Rd_entry_d n s g ∧ KPair_d M s k P ∧ Rd_entry_d i p P ∧ Rd_entry_d a y p

def ja_observe_m {d} (g i a y : Term d) : Formula 1 d := set[d] ⟪
  ∃ n s k P p, ⌜rd_entry0_m⌝ₚ(n, s, ⌜g⌝ₛ) ∧ ⌜kpair_m⌝ₚ(s, k, P) ∧
    ⌜rd_entry0_m⌝ₚ(⌜i⌝ₛ, p, P) ∧ ⌜rd_entry0_m⌝ₚ(⌜a⌝ₛ, ⌜y⌝ₛ, p)⟫
derive_free_closed ja_observe_m

theorem ja_observe_sat_l (hE : Extensional M) {d} (ρ : Env M d) (g i a y : Term d) :
    Formula.satisfies ρ (ja_observe_m g i a y) ↔ Ja_observe_d (g.eval ρ) (i.eval ρ) (a.eval ρ) (y.eval ρ) := by
  simp only [ja_observe_m, Ja_observe_d, Formula.satisfies_exists_iff, Formula.satisfies_conj_iff,
    rd_entry0_sat_l hE, kpair_sat_l M hE, Definitional.Term.eval_weaken]; rfl

def Ja_leg_d (E g i f : M.Domain) : Prop := (∀ p, M.mem p f → ∃ x y, KPair_d M p x y) ∧
  ∀ x y, Rd_entry_d x y f ↔ ∃ e n, Rd_entry_d i e E ∧ Rd_entry_d n x e ∧ Ja_observe_d g i n y

def ja_leg_m {d} (E g i f : Term d) : Formula 1 d := set[d] ⟪
  ⌜Formula.isRelation kpair_convention_l⌝ₚ(⌜f⌝ₛ) ∧ (∀ x y, ⌜rd_entry0_m⌝ₚ(x, y, ⌜f⌝ₛ) ↔
    ∃ e n, ⌜rd_entry0_m⌝ₚ(⌜i⌝ₛ, e, ⌜E⌝ₛ) ∧ ⌜rd_entry0_m⌝ₚ(n, x, e) ∧ ⌜ja_observe_m⌝ₚ(⌜g⌝ₛ, ⌜i⌝ₛ, n, y))⟫
derive_free_closed ja_leg_m

theorem ja_leg_sat_l (hKP : M.Models KP) {d} (ρ : Env M d) (E g i f : Term d) :
    Formula.satisfies ρ (ja_leg_m E g i f) ↔ Ja_leg_d (E.eval ρ) (g.eval ρ) (i.eval ρ) (f.eval ρ) := by
  simp only [ja_leg_m, Ja_leg_d, Formula.satisfies_conj_iff, Formula.satisfies_isRelation_iff (kp_pair_l hKP),
    Formula.satisfies_forall_iff, Formula.satisfies_iff_iff, Formula.satisfies_exists_iff,
    rd_entry0_sat_l hKP.1, ja_observe_sat_l hKP.1, Definitional.Term.eval_weaken]; rfl

theorem Ja_leg_d.unique_l (hKP : M.Models KP) {E g i f j : M.Domain}
    (hf : Ja_leg_d E g i f) (hj : Ja_leg_d E g i j) : f = j := by
  have rel : M.IsSetRelation (kp_pair_l hKP) f := hf.1
  exact rel.eq_of_pairMember_iff hKP.1 hj.1 (fun x y => (hf.2 x y).trans (hj.2 x y).symm)

variable (hZF : M.Models ZF)
local notation "I" => kp_pair_l (ZF.modelsKP hZF)

theorem ja_row_l {ω T Q G E Y W z π A R g B i c X V e d : M.Domain}
    (hω : M.IsOmega ω) (en : Ja_enum_d I ω ω Q E) (my : Smdl_d I d Y W)
    (space : Ja_space_d I ω T Q G E Y W z π A R) (fg : Fn0_d ω A g) (path : Ja_path_d ω T g B)
    (hi : M.mem i B) (hc : Rd_entry_d i c Q) (mx : Smdl_d I c X V) (he : Rd_entry_d i e E) :
    ∃ f, Smap_d I ω c d X Y f ∧ Ja_leg_d E g i f := by
  have enum := (en.rows i e c X V he hc mx.1).1
  have row n s k P p (hs : Rd_entry_d n s g) (hp : KPair_d M s k P) (hr : Rd_entry_d i p P) :
      Fn0_d k Y p := ((space.node_l hZF (fg.bound_l hs).2 hp).rows i p c X V e hr hc mx.1 he).1
  have total a (ha : M.mem a ω) : ∃ y, Ja_observe_d g i a y := by
    obtain ⟨n, s, k, P, hs, hp, hik, hak⟩ := path.wide i a hi ha
    obtain ⟨p, hr⟩ := ((space.node_l hZF (fg.bound_l hs).2 hp).domain i).mpr hik
    obtain ⟨y, _, hay⟩ := (row n s k P p hs hp hr).2.1 a hak
    exact ⟨y, n, s, k, P, p, hs, hp, hr, hay⟩
  have unique a u v (hu : Ja_observe_d g i a u) (hv : Ja_observe_d g i a v) : u = v := by
    obtain ⟨n, s, k, P, p, hs, hp, hr, hau⟩ := hu
    obtain ⟨m, t, l, Q', q, ht, hq, hr', hav⟩ := hv
    have eq {p q u v l : M.Domain} (hq : Fn0_d l Y q) (hau : Rd_entry_d a u p) (hav : Rd_entry_d a v q)
        (sub : M.MemberSubset p q) : u = v := by
      obtain ⟨r, hpair, hr⟩ := hau
      exact (fn0_function_l (ZF.modelsKP hZF) hq).1.2 a u v ⟨r, hpair, sub r hr⟩ hav
    rcases (hω.isOrdinal (ZF.modelsKP hZF)).wellOrder.linear.compare n (fg.bound_l hs).1 m (fg.bound_l ht).1 with hnm | hnm | hmn
    · have hn := hZF.1.eq_of_same_members n m hnm
      subst m
      have st := (fn0_function_l (ZF.modelsKP hZF) fg).1.2 n s t hs ht
      have pq := (kpair_injective_l M (st ▸ hp) hq).2
      have e := (space.node_l hZF (fg.bound_l ht).2 hq).function.2 i p q (pq ▸ hr) hr'
      exact eq (row n t l Q' q ht hq hr') hau hav (fun r hr => e ▸ hr)
    · exact eq (row m t l Q' q ht hq hr') hau hav
        (((path.chain n m s t hnm hs ht).read_l hp hq).2.2 i p q hr hr')
    · exact (eq (row n s k P p hs hp hr) hav hau
        (((path.chain m n t s hmn ht hs).read_l hq hp).2.2 i q p hr' hr)).symm
  let φ : BinarySchema 2 := { body := ja_observe_m (.bound 2) (.bound 3) (.bound 1) .newest }
  let ρ : Env M 2 := ⟨Fin.cases g (fun _ => i), fun _ => i⟩
  have sat a y : φ.denote ρ a y ↔ Ja_observe_d g i a y := ja_observe_sat_l hZF.1 ..
  obtain ⟨v, fv, vs⟩ := ZF.exists_setFunctionFromTo_of_denote hZF I φ ρ (source := ω) (target := Y)
    (fun a ha => (total a ha).imp fun y hy => (sat a y).mpr hy)
    (fun a _ u v hu hv => unique a u v ((sat a u).mp hu) ((sat a v).mp hv))
    (fun a y _ hy => by
      obtain ⟨n, s, k, P, p, hs, hp, hr, hay⟩ := (sat a y).mp hy
      exact ((row n s k P p hs hp hr).bound_l hay).2)
  have read a y : Rd_entry_d a y v ↔ Ja_observe_d g i a y :=
    (vs a y).trans ⟨fun h => (sat a y).mp h.2, fun h => by
      obtain ⟨n, s, k, P, p, hs, hp, hr, hay⟩ := h
      exact ⟨hω.transitive (ZF.modelsKP hZF) k (space.node_l hZF (fg.bound_l hs).2 hp).length a
        ((row n s k P p hs hp hr).bound_l hay).1, (sat a y).mpr ⟨n, s, k, P, p, hs, hp, hr, hay⟩⟩⟩
  let ψ : BinarySchema 1 := { body := rd_entry0_m .newest (.bound 1) (.bound 2) }
  let η : Env M 1 := ⟨fun _ => e, fun _ => e⟩
  have psat x n : ψ.denote η x n ↔ Rd_entry_d n x e := rd_entry0_sat_l hZF.1 ..
  obtain ⟨ι, fι, sect⟩ := ZF.ordinal_uniformize_l hZF ψ η (hω.isOrdinal (ZF.modelsKP hZF))
    (fun x hx => ((en.rows i e c X V he hc mx.1).2 x hx).elim fun n hn => ⟨n, (psat x n).mpr hn.2⟩)
    (fun x n _ hn => (enum.bound_l ((psat x n).mp hn)).1)
  obtain ⟨f, ff⟩ := cp0_exists_l (ZF.modelsKP hZF) fι (fn0_of_function_l (ZF.modelsKP hZF) fv)
  obtain ⟨o, ho⟩ := KP.exists_empty (ZF.modelsKP hZF)
  have branch n (hn : M.mem n ω) : ∃ p, At_node_d I ω X V Y W e o n p ∧ M.IsRestrictionOf I p v n := by
    obtain ⟨m, s, k, P, hs, hp, hik, hnk⟩ := path.wide i n hi hn
    have node := space.node_l hZF (fg.bound_l hs).2 hp
    obtain ⟨q, hq⟩ := (node.domain i).mpr hik
    obtain ⟨fn, coherent, elementary⟩ := node.rows i q c X V e hq hc mx.1 he
    have atnode : At_node_d I ω X V Y W e o k q := ⟨node.length, fn, coherent,
      fun _ _ _ _ _ _ _ ⟨r, _, hr⟩ => (ho r hr).elim, elementary⟩
    obtain ⟨p, pr⟩ := ZF.exists_restriction hZF I q n
    have pf := pr.isSetFunctionFromTo (fn0_function_l (ZF.modelsKP hZF) fn)
      (((hω.isOrdinal (ZF.modelsKP hZF)).mem node.length).transitive.memberSubset hnk)
    have sub : M.MemberSubset p q := (Descriptive.ds_restrict_iff_l I pf (fn0_function_l (ZF.modelsKP hZF) fn).1).mp pr
    refine ⟨p, atnode.prefix_l hZF hn (fn0_of_function_l (ZF.modelsKP hZF) pf) sub, pf.1.1, fun a y => ?_⟩
    refine (pr.2 a y).trans (and_congr_right fun ha => ?_)
    have hak := ((hω.isOrdinal (ZF.modelsKP hZF)).mem node.length).transitive n hnk a ha
    obtain ⟨u, _, hau⟩ := fn.2.1 a hak
    have hav := (read a u).mpr ⟨m, s, k, P, q, hs, hp, hq, hau⟩
    exact ⟨fun hay => (read a y).mpr ⟨m, s, k, P, q, hs, hp, hq, hay⟩,
      fun hay => fv.1.2 a u y hav hay ▸ hau⟩
  obtain ⟨elem, _, maps⟩ := at_decode_l hZF hω mx my enum fι (fun x n hn => (psat x n).mp (sect x n hn))
    (fn0_of_function_l (ZF.modelsKP hZF) fv) ff branch
  refine ⟨f, elem, elem.1.1.1.1, fun x y => ⟨?_, ?_⟩⟩
  · intro hxy
    obtain ⟨n, _, hxn⟩ := fι.2.1 x (ff.1.bound_l hxy).1
    exact ⟨e, n, he, (psat x n).mp (sect x n hxn),
      (read n y).mp ((ff.value_l fι (fn0_of_function_l (ZF.modelsKP hZF) fv) hxn).mp hxy)⟩
  · rintro ⟨e', n, he', hnx, hny⟩
    exact maps n x y (en.function.2 i e' e he' he ▸ hnx) ((read n y).mpr hny)

end YesMetaZFC.SetTheory.LargeCardinal

/-! ## 联合尝试枝解码出相容的完整初等嵌入列

每条腿都有唯一图，所以替代收集整列。不同腿的交换律在同一个较长节点
中检查；目标不必被嵌入像覆盖，正好适用于嵌回固定秩段的情形。
-/
namespace YesMetaZFC.SetTheory.LargeCardinal
open Definitional.Project InnerModel Internal
universe u
variable {M : Structure.{u}} (hZF : M.Models ZF)
local notation "I" => kp_pair_l (ZF.modelsKP hZF)

private theorem ja_common_l {ω T Q G E Y W z π A R g B i j a b u v : M.Domain}
    (h : It_order_d ω T) (space : Ja_space_d I ω T Q G E Y W z π A R)
    (fg : Fn0_d ω A g) (path : Ja_path_d ω T g B)
    (hu : Ja_observe_d g i a u) (hv : Ja_observe_d g j b v) :
    ∃ k P p q, Ja_node_d I ω T Q G E Y W z π k P ∧
      Rd_entry_d i p P ∧ Rd_entry_d j q P ∧ Rd_entry_d a u p ∧ Rd_entry_d b v q := by
  obtain ⟨n, s, k, P, p, hs, hp, hip, hau⟩ := hu
  obtain ⟨m, t, l, Q', q, ht, hq, hjq, hbv⟩ := hv
  have np := space.node_l hZF (fg.bound_l hs).2 hp
  have nq := space.node_l hZF (fg.bound_l ht).2 hq
  have move {i k l P Q' p a u} (np : Ja_node_d I ω T Q G E Y W z π k P)
      (nq : Ja_node_d I ω T Q G E Y W z π l Q') (hkl : Rd_entry_d k l T)
      (sub : ∀ i p q, Rd_entry_d i p P → Rd_entry_d i q Q' → M.MemberSubset p q)
      (hip : Rd_entry_d i p P) (hau : Rd_entry_d a u p) : ∃ q, Rd_entry_d i q Q' ∧ Rd_entry_d a u q := by
    obtain ⟨q, hiq⟩ := (nq.domain i).mpr (h.trans i k l ((np.domain i).mp ⟨p, hip⟩) hkl)
    obtain ⟨r, hr, hrp⟩ := hau
    exact ⟨q, hiq, r, hr, sub i p q hip hiq r hrp⟩
  rcases h.ordinal.wellOrder.linear.compare n (fg.bound_l hs).1 m (fg.bound_l ht).1 with eq | hnm | hmn
  · have eq := hZF.1.eq_of_same_members n m eq
    subst m
    have st := (fn0_function_l (ZF.modelsKP hZF) fg).1.2 n s t hs ht
    have pq := (kpair_injective_l M (st ▸ hp) hq).2
    exact ⟨l, Q', p, q, nq, pq ▸ hip, hjq, hau, hbv⟩
  · have ext := (path.chain n m s t hnm hs ht).read_l hp hq
    obtain ⟨p', hip', hau'⟩ := move np nq ext.2.1 ext.2.2 hip hau
    exact ⟨l, Q', p', q, nq, hip', hjq, hau', hbv⟩
  · have ext := (path.chain m n t s hmn ht hs).read_l hq hp
    obtain ⟨q', hjq', hbv'⟩ := move nq np ext.2.1 ext.2.2 hjq hbv
    exact ⟨k, P, p, q', np, hip, hjq', hau, hbv'⟩

theorem ja_decode_l {ω T Q G E Y W z π A R g B d : M.Domain}
    (hω : M.IsOmega ω) (h : It_diagram_d (kp_pair_l (ZF.modelsKP hZF)) ω ω T Q G) (en : Ja_enum_d I ω ω Q E)
    (my : Smdl_d I d Y W) (space : Ja_space_d I ω T Q G E Y W z π A R)
    (fg : Fn0_d ω A g) (path : Ja_path_d ω T g B) :
    ∃ P, It_embedding_d (kp_pair_l (ZF.modelsKP hZF)) ω B Q G d Y W P ∧ ∀ i f, Rd_entry_d i f P ↔ M.mem i B ∧ Ja_leg_d E g i f := by
  let φ : BinarySchema 2 := { body := ja_leg_m (.bound 2) (.bound 3) (.bound 1) .newest }
  let ρ : Env M 2 := ⟨Fin.cases E (fun _ => g), fun _ => g⟩
  have sat i f : φ.denote ρ i f ↔ Ja_leg_d E g i f := ja_leg_sat_l (ZF.modelsKP hZF) ..
  have total i (hi : M.mem i B) : ∃ f, φ.denote ρ i f := by
    obtain ⟨c, X, V, hc, mx⟩ := h.model_l hZF (path.branch.subset i hi)
    obtain ⟨e, he⟩ := (en.domain i).mp (path.branch.subset i hi)
    obtain ⟨f, _, hf⟩ := ja_row_l hZF hω en my space fg path hi hc mx he
    exact ⟨f, (sat i f).mpr hf⟩
  have unique i f j (hf : φ.denote ρ i f) (hj : φ.denote ρ i j) : f = j :=
    ((sat i f).mp hf).unique_l (ZF.modelsKP hZF) ((sat i j).mp hj)
  obtain ⟨D, hd⟩ := ZF.exists_functionalImage hZF φ ρ B total unique
  obtain ⟨P, pf, ps⟩ := ZF.exists_setFunctionFromTo_of_denote hZF I φ ρ total (fun i _ => unique i)
    (fun i f hi hf => (hd f).mpr ⟨i, hi, hf⟩)
  have read i f : Rd_entry_d i f P ↔ M.mem i B ∧ Ja_leg_d E g i f :=
    (ps i f).trans (and_congr_right fun _ => sat i f)
  have typed i f c X V (hf : Rd_entry_d i f P) (hc : Rd_entry_d i c Q) (mx : Smdl_d I c X V) :
      Smap_d I ω c d X Y f := by
    obtain ⟨e, he⟩ := (en.domain i).mp (path.branch.subset i ((read i f).mp hf).1)
    obtain ⟨j, hj, js⟩ := ja_row_l hZF hω en my space fg path ((read i f).mp hf).1 hc mx he
    exact js.unique_l (ZF.modelsKP hZF) ((read i f).mp hf).2 ▸ hj
  refine ⟨P, ⟨my, pf.1, pf.2.1, typed, ?_⟩, read⟩
  intro i j f u v hf hu hv x y a hxy hya
  obtain ⟨ci, X, S, hci, mx⟩ := h.model_l hZF (path.branch.subset i ((read i u).mp hu).1)
  obtain ⟨cj, Z, V, hcj, mz⟩ := h.model_l hZF (path.branch.subset j ((read j v).mp hv).1)
  have elem := typed i u ci X S hu hci mx
  have hx := (h.elementary i j f ci X S cj Z V hf hci hcj mx mz).1.1.input_mem_of_pairMember hxy
  obtain ⟨b, _, hxb⟩ := elem.1.1.2.2 x hx
  obtain ⟨e, n, he, hnx, hnb⟩ := (((read i u).mp hu).2.2 x b).mp hxb
  obtain ⟨e', m, he', hmy, hma⟩ := (((read j v).mp hv).2.2 y a).mp hya
  obtain ⟨k, H, p, q, node, hp, hq, hnp, hmq⟩ := ja_common_l hZF h.order space fg path hnb hma
  exact node.commute i j p q e e' f n m x y b a hp hq he he' hf hnx hmy hxy hnp hmq ▸ hxb

/-- 根行的原图由有限限制恢复；这里只需要原图是全定义函数。 -/
theorem ja_root_l {ω T Q G E Y W z π A R g B P c X V : M.Domain}
    (en : Ja_enum_d I ω ω Q E) (space : Ja_space_d I ω T Q G E Y W z π A R)
    (fg : Fn0_d ω A g) (path : Ja_path_d ω T g B) (hz : M.mem z B)
    (hc : Rd_entry_d z c Q) (mx : Smdl_d I c X V) (fπ : Fn0_d X Y π)
    (maps : ∀ i f, Rd_entry_d i f P ↔ M.mem i B ∧ Ja_leg_d E g i f)
    (fn : ∀ f, Rd_entry_d z f P → Fn0_d X Y f) (domain : ∃ f, Rd_entry_d z f P) : Rd_entry_d z π P := by
  obtain ⟨f, hf⟩ := domain
  obtain ⟨e, he⟩ := (en.domain z).mp (path.branch.subset z hz)
  have eq : π = f := fπ.ext_l hZF.1 (fn f hf) (fun x hx => by
    obtain ⟨y, hy, hxy⟩ := fπ.2.1 x hx
    obtain ⟨a, ha, hax⟩ := (en.rows z e c X V he hc mx.1).2 x hx
    obtain ⟨n, s, k, H, hs, hp, hzk, hak⟩ := path.wide z a hz ha
    have node := space.node_l hZF (fg.bound_l hs).2 hp
    obtain ⟨p, hzp⟩ := (node.domain z).mpr hzk
    have hay := node.root p c X V e hzp hc mx.1 he a hak x hx y hy hax hxy
    exact ⟨y, hxy, (((maps z f).mp hf).2.2 x y).mpr ⟨e, a, he, hax, n, s, k, H, p, hs, hp, hzp, hay⟩⟩)
  exact eq.symm ▸ hf

end YesMetaZFC.SetTheory.LargeCardinal

/-! ## 失败的返回嵌入产生联合尝试秩

任何内部下降链都解码为实际共尾枝、传递直接极限及满足根复合式的返回嵌入。
因此反例的尝试关系内部良基，原良基递归给出实际序数值秩函数。
-/
namespace YesMetaZFC.SetTheory.LargeCardinal
open Definitional.Project InnerModel Internal
universe u
variable {M : Structure.{u}} (hZF : M.Models ZF)
local notation "I" => kp_pair_l (ZF.modelsKP hZF)

theorem ja_counterexample_rank_l {ω T Q G E Y W z π c₀ X₀ V₀ d : M.Domain}
    (hω : M.IsOmega ω) (dc : Dc_d I ω) (h : It_diagram_d (kp_pair_l (ZF.modelsKP hZF)) ω ω T Q G)
    (en : Ja_enum_d I ω ω Q E) (hz : ∀ x, ¬ M.mem x z)
    (hc : Rd_entry_d z c₀ Q) (mx : Smdl_d I c₀ X₀ V₀) (source : It_source_d hZF ω c₀)
    (my : Smem_d I d Y W) (pi : Fn0_d X₀ Y π) (bad : ¬ It_return_d hZF ω z T Q G d Y π) :
    ∃ A R β F, Ja_space_d I ω T Q G E Y W z π A R ∧ M.IsOrdinal β ∧
      M.IsSetFunctionFromTo I F A β ∧ Wr_d I A R F := by
  obtain ⟨A, R, space⟩ := ja_space_l hZF hω h en (Y := Y) (W := W) (z := z) (π := π)
  have wf : Wf_rel_d A R := wf_of_no_desc_l hZF dc (fun g fg desc => by
    obtain ⟨B, path⟩ := ja_path_l hZF hω h.order space fg desc
    obtain ⟨P, maps, ps⟩ := ja_decode_l hZF hω h en my.1 space fg path
    have hzω := (h.model_domain z).mpr ⟨c₀, hc⟩
    obtain ⟨k, hk, _⟩ := path.branch.cofinal z hzω
    have hzB := path.branch.down z k (h.order.root_l hZF hz k (path.branch.subset k hk)) hk
    have root := ja_root_l hZF en space fg path hzB hc mx pi ps
      (fun f hf => fn0_of_function_l (ZF.modelsKP hZF) (maps.elementary z f c₀ X₀ V₀ hf hc mx).1.1)
      ((maps.domain z).mp hzB)
    exact bad (it_embedding_return_l hZF hω h path.branch hzB hc source my maps root))
  obtain ⟨β, F, hb, hf, _, rank⟩ := wr_exists_l I hZF wf
  exact ⟨A, R, β, F, space, hb, hf, rank⟩

end YesMetaZFC.SetTheory.LargeCardinal
