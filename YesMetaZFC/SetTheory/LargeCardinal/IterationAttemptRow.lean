import YesMetaZFC.SetTheory.LargeCardinal.IterationAttemptPath
import YesMetaZFC.SetTheory.OrdinalChoice

/-! # 联合枝各行解码为完整初等嵌入

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
    rcases (hω.isOrdinal hZF).wellOrder.linear.compare n (fg.bound_l hs).1 m (fg.bound_l ht).1 with hnm | hnm | hmn
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
      exact ⟨hω.transitive hZF k (space.node_l hZF (fg.bound_l hs).2 hp).length a
        ((row n s k P p hs hp hr).bound_l hay).1, (sat a y).mpr ⟨n, s, k, P, p, hs, hp, hr, hay⟩⟩⟩
  let ψ : BinarySchema 1 := { body := rd_entry0_m .newest (.bound 1) (.bound 2) }
  let η : Env M 1 := ⟨fun _ => e, fun _ => e⟩
  have psat x n : ψ.denote η x n ↔ Rd_entry_d n x e := rd_entry0_sat_l hZF.1 ..
  obtain ⟨ι, fι, sect⟩ := ZF.ordinal_uniformize_l hZF ψ η (hω.isOrdinal hZF)
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
      (((hω.isOrdinal hZF).mem node.length).transitive.memberSubset hnk)
    have sub : M.MemberSubset p q := (Descriptive.ds_restrict_iff_l I pf (fn0_function_l (ZF.modelsKP hZF) fn).1).mp pr
    refine ⟨p, atnode.prefix_l hZF hn (fn0_of_function_l (ZF.modelsKP hZF) pf) sub, pf.1.1, fun a y => ?_⟩
    refine (pr.2 a y).trans (and_congr_right fun ha => ?_)
    have hak := ((hω.isOrdinal hZF).mem node.length).transitive n hnk a ha
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
