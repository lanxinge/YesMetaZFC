import YesMetaZFC.SetTheory.LargeCardinal.IterationStep
import YesMetaZFC.SetTheory.Card.FiniteSequenceCountable
import YesMetaZFC.SetTheory.Card.OrdinalImage
import YesMetaZFC.SetTheory.Notation

/-! # 可数源与可数支撑的实际超幂可数

各分量投影由原测度图唯一决定，先用替代收集投影，再把极限写成
有限支撑与源内代表的可数集合的像。只用 ZF，不选取各商类的代表。
-/
namespace YesMetaZFC.SetTheory.LargeCardinal
open Definitional.Project InnerModel Internal
universe u
variable {M : Structure.{u}} (hZF : M.Models ZF)
local notation "I" => kp_pair_l (ZF.modelsKP hZF)

private def Ec_project_d (ω κ L X R F Z a p : M.Domain) : Prop := ∃ c n D U G C V,
  Rd_entry_d a c Z ∧ M.mem n ω ∧ Fn0_d n L a ∧ Ep_space_d κ n D ∧ Rd_entry_d a U F ∧
    (∀ f, M.mem f G ↔ M.mem f X ∧ Fn0_d D X f) ∧ Rp_model_d I D X U R c G p C V

private def ec_project_m {d} (ω κ L X R F Z a p : Term d) : Formula 1 d := set[d] ⟪
  ∃ c n D U G C V, ⌜rd_entry0_m⌝ₚ(⌜a⌝ₛ, c, ⌜Z⌝ₛ) ∧ n ∈ ⌜ω⌝ₛ ∧ ⌜fn0_m⌝ₚ(n, ⌜L⌝ₛ, ⌜a⌝ₛ) ∧
    ⌜ep_space_m⌝ₚ(⌜κ⌝ₛ, n, D) ∧ ⌜rd_entry0_m⌝ₚ(⌜a⌝ₛ, U, ⌜F⌝ₛ) ∧
    (∀ f, f ∈ G ↔ f ∈ ⌜X⌝ₛ ∧ ⌜fn0_m⌝ₚ(D, ⌜X⌝ₛ, f)) ∧
    ⌜rp_model_m (𝒞 := kpair_convention_l)⌝ₚ(D, ⌜X⌝ₛ, U, ⌜R⌝ₛ, c, G, ⌜p⌝ₛ, C, V)⟫
derive_free_closed ec_project_m

private theorem ec_project_sat_l {d} (ρ : Env M d) (ω κ L X R F Z a p : Term d) :
    Formula.satisfies ρ (ec_project_m ω κ L X R F Z a p) ↔ Ec_project_d hZF
      (ω.eval ρ) (κ.eval ρ) (L.eval ρ) (X.eval ρ) (R.eval ρ) (F.eval ρ) (Z.eval ρ) (a.eval ρ) (p.eval ρ) := by
  simp only [ec_project_m, Ec_project_d, Formula.satisfies_exists_iff, Formula.satisfies_conj_iff,
    rd_entry0_sat_l hZF.1, Formula.satisfies_mem_iff, fn0_sat_l hZF.1, ep_space_sat_l hZF.1,
    Formula.satisfies_forall_iff, Formula.satisfies_iff_iff, rp_model_sat_l I hZF.1, Definitional.Term.eval_weaken]; rfl

private theorem ec_project_unique_l {ω κ L X R F Z a p q : M.Domain} (ff : M.IsSetFunction I F)
    (hp : Ec_project_d hZF ω κ L X R F Z a p) (hq : Ec_project_d hZF ω κ L X R F Z a q) : p = q := by
  obtain ⟨c, n, D, U, G, C, V, _, _, ha, hd, hu, hg, mp⟩ := hp
  obtain ⟨c', n', D', U', G', C', V', _, _, ha', hd', hu', hg', mq⟩ := hq
  have en := ha'.domain_eq_l hZF.1 ha
  subst n'
  have ed := hZF.1.eq_of_same_members D' D (fun x => (hd' x).trans (hd x).symm)
  subst D'
  have eu := ff.2 a U' U hu' hu
  subst U'
  have eg := hZF.1.eq_of_same_members G' G (fun f => (hg' f).trans (hg f).symm)
  subst G'
  exact mp.map.projection.1.1.eq_of_pairMember_iff hZF.1 mq.map.projection.1.1
    (fun f B => (mp.map.classes f B).trans (mq.map.classes f B).symm)

private def ec_count_image_m {d} (P q v E : Term d) : Formula 1 d := set[d] ⟪
  ∃ a f r B u, ⌜kpair_m⌝ₚ(⌜v⌝ₛ, a, f) ∧ ⌜rd_entry0_m⌝ₚ(a, r, ⌜P⌝ₛ) ∧
    ⌜rd_entry0_m⌝ₚ(f, B, r) ∧ ⌜kpair_m⌝ₚ(u, a, B) ∧ ⌜rd_entry0_m⌝ₚ(u, ⌜E⌝ₛ, ⌜q⌝ₛ)⟫
derive_free_closed ec_count_image_m

theorem ep_countable_l {ω κ L X R F J O Z A p T S q C W : M.Domain}
    (hω : M.IsOmega ω) (ff : M.IsSetFunction I F) (cx : M.CardinalLessOrEqual I X ω) (cl : M.CardinalLessOrEqual I L ω)
    (h : Ep_system_d I ω κ L X R F J O Z A p T S) (limit : Di_limit_d A p T S q C W) :
    M.CardinalLessOrEqual I C ω := by
  have small {B D} (sub : M.MemberSubset B D) (hd : M.CardinalLessOrEqual I D ω) : M.CardinalLessOrEqual I B ω := by
    obtain ⟨f, hf⟩ := ZF.exists_inclusionInjection hZF I sub
    obtain ⟨g, hg⟩ := hd
    exact ZF.exists_compositionInjection hZF I hf hg
  obtain ⟨V, hv, cv⟩ := ZF.fseq_countable_space_l I hZF hω cl
  have cj : M.CardinalLessOrEqual I J ω := small (fun a ha => by
    obtain ⟨n, hn, hf, _⟩ := (h.indices a).mp ha
    exact (hv a).mpr ⟨n, hn, fn0_function_l (ZF.modelsKP hZF) hf⟩) cv
  obtain ⟨H, hh⟩ := ZF.exists_cartesianProduct hZF I J X
  have ch := ZF.countable_product_l I hZF hω cj cx hh
  obtain ⟨D, hz⟩ := h.codes
  have models := h.components
  let φ : BinarySchema 7 := { body := (ec_project_m (.bound 2) (.bound 3) (.bound 4) (.bound 5)
    (.bound 6) (.bound 7) (.bound 8) (.bound 1) .newest) }
  let ρ : Env M 7 := ⟨Fin.cases ω (Fin.cases κ (Fin.cases L (Fin.cases X (Fin.cases R (Fin.cases F (fun _ => Z)))))), fun _ => ω⟩
  have sat a r : φ.denote ρ a r ↔ Ec_project_d hZF ω κ L X R F Z a r := ec_project_sat_l hZF ..
  have total a (ha : M.mem a J) : ∃ r, φ.denote ρ a r := by
    obtain ⟨c, _, hc⟩ := hz.2.1 a ha
    obtain ⟨n, D, U, G, r, C, V, hn, ha, hd, hu, hg, mp⟩ := models a c hc
    exact ⟨r, (sat a r).mpr ⟨c, n, D, U, G, C, V, hc, hn, ha, hd, hu, hg, mp⟩⟩
  have unique a r s (hr : φ.denote ρ a r) (hs : φ.denote ρ a s) : r = s :=
    ec_project_unique_l hZF ff ((sat a r).mp hr) ((sat a s).mp hs)
  obtain ⟨V, vs⟩ := ZF.exists_functionalImage hZF φ ρ J total unique
  obtain ⟨P, pf, ps⟩ := ZF.exists_setFunctionFromTo_of_denote hZF I φ ρ total (fun a _ => unique a)
    (fun a r ha hr => (vs r).mpr ⟨a, ha, hr⟩)
  have proj a r (hr : Rd_entry_d a r P) := (sat a r).mp ((ps a r).mp hr).2
  let ψ : BinarySchema 2 := { body := ec_count_image_m (.bound 2) (.bound 3) (.bound 1) .newest }
  let η : Env M 2 := ⟨Fin.cases P (fun _ => q), fun _ => q⟩
  have read v E : ψ.denote η v E ↔ ∃ a f r B u, KPair_d M v a f ∧ Rd_entry_d a r P ∧
      Rd_entry_d f B r ∧ KPair_d M u a B ∧ Rd_entry_d u E q := by
    simp only [ψ, ec_count_image_m, BinarySchema.denote, Formula.satisfies_exists_iff, Formula.satisfies_conj_iff,
      kpair_sat_l M hZF.1, rd_entry0_sat_l hZF.1, Definitional.Term.eval_weaken]; rfl
  let θ : UnarySchema 2 := { body := .existsE ψ.body, freeClosed := by simp -implicitDefEqProofs [Definitional.Formula.FreeClosed, ψ.freeClosed] }
  obtain ⟨B, bs⟩ := ZF.separation_exists_d hZF θ η H
  have legal v : M.mem v B ↔ M.mem v H ∧ ∃ E, ψ.denote η v E := by
    simpa only [θ, UnarySchema.denote, Formula.satisfies_exists_iff] using! bs v
  obtain ⟨f, fs, spec⟩ := ZF.exists_setFunctionFromTo_of_denote hZF I ψ η (source := B) (target := C)
    (fun v hv => ((legal v).mp hv).2) (by
      intro v _ E D he hd
      obtain ⟨a, f, r, B, u, hv, hr, hfr, hu, he⟩ := (read v E).mp he
      obtain ⟨a', f', r', B', u', hv', hr', hfr', hu', hd⟩ := (read v D).mp hd
      obtain ⟨ea, ef⟩ := kpair_injective_l M hv' hv
      subst a' f'
      have er := pf.1.2 a r' r hr' hr
      subst r'
      obtain ⟨_, _, _, _, _, _, _, _, _, _, _, _, _, mp⟩ := proj a r hr
      have eb := mp.map.projection.1.2 f B' B hfr' hfr
      subst B'
      exact (fn0_function_l (ZF.modelsKP hZF) limit.projection).1.2 u E D he (kpair_unique_l M hZF.1 hu' hu ▸ hd))
    (fun v E _ he => ((read v E).mp he).elim fun _ ha => ha.elim fun _ hf => hf.elim fun _ hr =>
      hr.elim fun _ hb => hb.elim fun _ hu => (limit.projection.bound_l hu.2.2.2.2).2)
  have onto E (he : M.mem E C) : ∃ v, M.mem v B ∧ Rd_entry_d v E f := by
    obtain ⟨u, hu⟩ := (limit.range E).mp he
    obtain ⟨a, D, hp, atD⟩ := (h.nodes u).mp (limit.projection.bound_l hu).1
    have ha := (h.projection.bound_l ((h.index u a D hp).mpr (limit.projection.bound_l hu).1)).2
    obtain ⟨r, _, har⟩ := pf.2.2 a ha
    obtain ⟨c, n, K, U, G, D', V, hac, _, _, _, _, hg, mp⟩ := proj a r har
    have hd := (ep_at_read_l hz hac mp.code.1).mp atD
    obtain ⟨g, hgr⟩ := (mp.map.range D).mp hd
    have hgX := ((hg g).mp (mp.map.projection.input_mem_of_pairMember hgr)).1
    obtain ⟨v, hv⟩ := (I).total a g
    have vv := (read v E).mpr ⟨a, g, r, D, u, hv, har, hgr, hp, hu⟩
    have vb := (legal v).mpr ⟨(hh v).mpr ⟨a, ha, g, hgX, hv⟩, E, vv⟩
    exact ⟨v, vb, (spec v E).mpr ⟨vb, vv⟩⟩
  exact ZF.ordinal_image_bound_l I hZF (hω.isOrdinal hZF) (small (fun v hv => ((legal v).mp hv).1) ch) fs onto

theorem It_ultra_d.countable_l {ω κ L F c d j X R Y S : M.Domain} (hω : M.IsOmega ω)
    (ff : M.IsSetFunction I F) (cx : M.CardinalLessOrEqual I X ω) (cl : M.CardinalLessOrEqual I L ω)
    (mx : Smdl_d I c X R) (my : Smdl_d I d Y S) (edge : It_ultra_d hZF ω κ L F c d j) : M.CardinalLessOrEqual I Y ω := by
  obtain ⟨X', R', Y', S', J, O, Z, A, p, T, V, q, b, C, W, _, e,
    mx', my', sys, limit, _, _, bij, _⟩ := edge
  obtain ⟨ex, er⟩ := smdl_unique_l I mx'.1 mx
  obtain ⟨ey, es⟩ := smdl_unique_l I my'.1 my
  subst X' R' Y' S'
  exact ZF.ordinal_image_bound_l I hZF (hω.isOrdinal hZF) (ep_countable_l hZF hω ff cx cl sys limit) bij.1.1 bij.2

end YesMetaZFC.SetTheory.LargeCardinal
