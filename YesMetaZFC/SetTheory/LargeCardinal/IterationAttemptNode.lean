import YesMetaZFC.SetTheory.LargeCardinal.IterationAttempt

/-! # 从末结点嵌入实际构造联合尝试节点

每一行由原树嵌入、末结点嵌入及既有枚举复合，再截取有限定义域。
各行的图唯一，替代一次收集全部前驱；没有选择嵌入的额外参数。
-/
namespace YesMetaZFC.SetTheory.LargeCardinal
open Definitional.Project InnerModel Internal
universe u
variable {M : Structure.{u}}

def Ja_value_d (G E k j i a y : M.Domain) : Prop := ∃ e f x v,
  Rd_entry_d i e E ∧ It_map_d G i k f ∧ Rd_entry_d a x e ∧ Rd_entry_d x v f ∧ Rd_entry_d v y j

def ja_value_m {d} (G E k j i a y : Term d) : Formula 1 d := set[d] ⟪
  ∃ e f x v, ⌜rd_entry0_m⌝ₚ(⌜i⌝ₛ, e, ⌜E⌝ₛ) ∧ ⌜it_map_m⌝ₚ(⌜G⌝ₛ, ⌜i⌝ₛ, ⌜k⌝ₛ, f) ∧
    ⌜rd_entry0_m⌝ₚ(⌜a⌝ₛ, x, e) ∧ ⌜rd_entry0_m⌝ₚ(x, v, f) ∧ ⌜rd_entry0_m⌝ₚ(v, ⌜y⌝ₛ, ⌜j⌝ₛ)⟫
derive_free_closed ja_value_m

theorem ja_value_sat_l (hE : Extensional M) {d} (ρ : Env M d) (G E k j i a y : Term d) :
    Formula.satisfies ρ (ja_value_m G E k j i a y) ↔
      Ja_value_d (G.eval ρ) (E.eval ρ) (k.eval ρ) (j.eval ρ) (i.eval ρ) (a.eval ρ) (y.eval ρ) := by
  simp only [ja_value_m, Ja_value_d, Formula.satisfies_exists_iff, Formula.satisfies_conj_iff,
    rd_entry0_sat_l hE, it_map_sat_l hE, Definitional.Term.eval_weaken]; rfl

private def ja_lift_m {d} (G E k j Y i p : Term d) : Formula 1 d := set[d] ⟪
  ⌜fn0_m⌝ₚ(⌜k⌝ₛ, ⌜Y⌝ₛ, ⌜p⌝ₛ) ∧ (∀ a y, ⌜rd_entry0_m⌝ₚ(a, y, ⌜p⌝ₛ) ↔
    a ∈ ⌜k⌝ₛ ∧ ⌜ja_value_m⌝ₚ(⌜G⌝ₛ, ⌜E⌝ₛ, ⌜k⌝ₛ, ⌜j⌝ₛ, ⌜i⌝ₛ, a, y))⟫
derive_free_closed ja_lift_m

variable (hZF : M.Models ZF)
local notation "I" => kp_pair_l (ZF.modelsKP hZF)

theorem ja_node_of_l {ω α T Q G E Y W z π k c X R d j : M.Domain}
    (hω : M.IsOmega ω) (h : It_diagram_d hZF ω α T Q G) (en : Ja_enum_d I ω α Q E)
    (hk : M.mem k ω) (hc : Rd_entry_d k c Q) (mx : Smdl_d I c X R) (my : Smdl_d I d Y W)
    (hj : Smap_d I ω c d X Y j)
    (root : ∀ x y, Rd_entry_d x y π → ∃ f v, It_map_d G z k f ∧ Rd_entry_d x v f ∧ Rd_entry_d v y j) :
    ∃ P, Ja_node_d I ω T Q G E Y W z π k P ∧
      ∀ i p, Rd_entry_d i p P → ∀ a y, Rd_entry_d a y p ↔ M.mem a k ∧ Ja_value_d G E k j i a y := by
  let θ : UnarySchema 2 := { body := rd_entry0_m .newest (.bound 1) (.bound 2) }
  obtain ⟨B, bs⟩ := ZF.separation_exists_d hZF θ ⟨Fin.cases k (fun _ => T), fun _ => k⟩ α
  have pred i : M.mem i B ↔ Rd_entry_d i k T := by
    have b : M.mem i B ↔ M.mem i α ∧ Rd_entry_d i k T := by
      simpa only [θ, UnarySchema.denote, rd_entry0_sat_l hZF.1] using! bs i
    exact b.trans ⟨And.right, fun hi => ⟨(h.order.bound i k hi).1, hi⟩⟩
  obtain ⟨S, space⟩ := ZF.exists_functionSpace hZF I k Y
  let φ : BinarySchema 5 := { body := ja_lift_m (.bound 4) (.bound 5) (.bound 2) (.bound 6) (.bound 3) (.bound 1) .newest }
  let ρ : Env M 5 := ⟨Fin.cases k (Fin.cases Y (Fin.cases G (Fin.cases E (fun _ => j)))), fun _ => k⟩
  have sat i p : φ.denote ρ i p ↔ Fn0_d k Y p ∧
      ∀ a y, Rd_entry_d a y p ↔ M.mem a k ∧ Ja_value_d G E k j i a y := by
    simp only [φ, ja_lift_m, BinarySchema.denote, Formula.satisfies_conj_iff, fn0_sat_l hZF.1,
      Formula.satisfies_forall_iff, Formula.satisfies_iff_iff, rd_entry0_sat_l hZF.1,
      Formula.satisfies_mem_iff, ja_value_sat_l hZF.1]; rfl
  have full i b A V e f (hb : Rd_entry_d i b Q) (ma : Smdl_d I b A V)
      (he : Rd_entry_d i e E) (hf : It_map_d G i k f) :
      ∃ v, Smap_d I ω b d A Y v ∧ It_comp_d f j v ∧ ∀ a y,
        Ja_value_d G E k j i a y ↔ ∃ x, Rd_entry_d a x e ∧ Rd_entry_d x y v := by
    obtain ⟨v, hv, vs⟩ := it_comp_elementary_l hZF (h.elementary i k f b A V c X R hf hb hc ma mx) hj
    refine ⟨v, hv, vs, fun a y => ⟨?_, ?_⟩⟩
    · rintro ⟨e', f', x, t, he', hf', hax, hxt, hty⟩
      exact ⟨x, en.function.2 i e' e he' he ▸ hax,
        (vs.2 x y).mpr ⟨t, h.map_unique_l hZF hf' hf ▸ hxt, hty⟩⟩
    · rintro ⟨x, hax, hxy⟩
      obtain ⟨t, hxt, hty⟩ := (vs.2 x y).mp hxy
      exact ⟨e, f, x, t, he, hf, hax, hxt, hty⟩
  have total i (hi : M.mem i B) : ∃ p, φ.denote ρ i p := by
    have hi := (pred i).mp hi
    obtain ⟨b, A, V, hb, ma⟩ := h.model_l hZF (h.order.bound i k hi).1
    obtain ⟨e, he⟩ := (en.domain i).mp (h.order.bound i k hi).1
    obtain ⟨f, hf⟩ := h.map_l hZF hi
    obtain ⟨v, hv, _, vs⟩ := full i b A V e f hb ma he hf
    have ef := (en.rows i e b A V he hb ma.1).1
    obtain ⟨q, hq⟩ := cp0_exists_l (ZF.modelsKP hZF) ef (fn0_of_function_l (ZF.modelsKP hZF) hv.1.1)
    obtain ⟨p, hp⟩ := ZF.exists_restriction hZF I q k
    have pf := hp.isSetFunctionFromTo (fn0_function_l (ZF.modelsKP hZF) hq.1) (hω.transitive hZF k hk)
    refine ⟨p, (sat i p).mpr ⟨fn0_of_function_l (ZF.modelsKP hZF) pf, fun a y => ?_⟩⟩
    refine (hp.2 a y).trans (and_congr_right fun ha => ?_)
    obtain ⟨x, _, hax⟩ := ef.2.1 a (hω.transitive hZF k hk a ha)
    refine (hq.value_l ef (fn0_of_function_l (ZF.modelsKP hZF) hv.1.1) hax).trans ⟨fun hxy => (vs a y).mpr ⟨x, hax, hxy⟩, ?_⟩
    intro hy
    obtain ⟨x', hax', hxy⟩ := (vs a y).mp hy
    exact (fn0_function_l (ZF.modelsKP hZF) ef).1.2 a x' x hax' hax ▸ hxy
  have unique i p q (hp : φ.denote ρ i p) (hq : φ.denote ρ i q) : p = q := by
    obtain ⟨pf, ps⟩ := (sat i p).mp hp
    obtain ⟨qf, qs⟩ := (sat i q).mp hq
    exact pf.ext_l hZF.1 qf (fun a ha => (pf.2.1 a ha).elim fun y hy =>
      ⟨y, hy.2, (qs a y).mpr ((ps a y).mp hy.2)⟩)
  obtain ⟨P, pf, ps⟩ := ZF.exists_setFunctionFromTo_of_denote hZF I φ ρ total
    (fun i _ => unique i) (fun i p _ hp => (space p).mpr (fn0_function_l (ZF.modelsKP hZF) ((sat i p).mp hp).1))
  have entry i p (hi : Rd_entry_d i p P) := (sat i p).mp ((ps i p).mp hi).2
  have dom i : (∃ p, Rd_entry_d i p P) ↔ Rd_entry_d i k T := (pf.2.1 i).symm.trans (pred i)
  have part i p b A V e f v (hi : Rd_entry_d i p P) (hb : Rd_entry_d i b Q)
      (ma : Smdl_d I b A V) (he : Rd_entry_d i e E) (hf : It_map_d G i k f)
      (hv : Smap_d I ω b d A Y v) (vs : It_comp_d f j v) : Cp0_d k A Y e v p := by
    refine ⟨(entry i p hi).1, fun a ha => ?_⟩
    obtain ⟨x, hx, hax⟩ := (en.rows i e b A V he hb ma.1).1.2.1 a (hω.transitive hZF k hk a ha)
    obtain ⟨y, hy, hxy⟩ := hv.1.1.2.2 x hx
    obtain ⟨t, hxt, hty⟩ := (vs.2 x y).mp hxy
    exact ⟨x, hx, y, hy, hax, hxy, (entry i p hi).2 a y |>.mpr ⟨ha, e, f, x, t, he, hf, hax, hxt, hty⟩⟩
  have rows : Ja_rows_d I ω Q E Y W k P := by
    intro i p b A V e hi hb hp he
    obtain ⟨A', V', ma⟩ := h.models i b hb
    obtain ⟨ea, ev⟩ := kpair_injective_l M ma.1 hp
    subst A' V'
    obtain ⟨f, hf⟩ := h.map_l hZF ((dom i).mp ⟨p, hi⟩)
    obtain ⟨v, hv, vs, _⟩ := full i b A V e f hb ma he hf
    obtain ⟨o, ho⟩ := KP.exists_empty (ZF.modelsKP hZF)
    have node := at_node_of_l hZF hω ma my hv (en.rows i e b A V he hb ma.1).1
      (τ := o) (fun _ _ ⟨r, _, hr⟩ => (ho r hr).elim) hk (part i p b A V e f v hi hb ma he hf hv vs)
    exact ⟨node.function, node.coherent, node.elementary⟩
  refine ⟨P, ⟨hk, pf.1, dom, rows, ?_, ?_⟩, fun i p hi => (entry i p hi).2⟩
  · intro p b A V e hp _ _ he a ha x _ y _ hax hxy
    obtain ⟨f, v, hf, hxv, hvy⟩ := root x y hxy
    exact ((entry z p hp).2 a y).mpr ⟨ha, e, f, x, v, he, hf, hax, hxv, hvy⟩
  · intro i l p q e f g a b x y u v hp hq he hf hg hax hby hxy hau hbv
    obtain ⟨_, e', fi, x', s, he', hfi, hax', hxs, hsu⟩ := ((entry i p hp).2 a u).mp hau
    obtain ⟨_, f', fl, y', t, hf', hfl, hby', hyt, htv⟩ := ((entry l q hq).2 b v).mp hbv
    obtain ⟨ci, A, U, hci, ma⟩ := h.model_l hZF (h.order.bound i k ((dom i).mp ⟨p, hp⟩)).1
    obtain ⟨cl, C, V, hcl, mb⟩ := h.model_l hZF (h.order.bound l k ((dom l).mp ⟨q, hq⟩)).1
    have xe := (fn0_function_l (ZF.modelsKP hZF) (en.rows i e ci A U he hci ma.1).1).1.2 a x' x
      (en.function.2 i e' e he' he ▸ hax') hax
    have ye := (fn0_function_l (ZF.modelsKP hZF) (en.rows l f cl C V hf hcl mb.1).1).1.2 b y' y
      (en.function.2 l f' f hf' hf ▸ hby') hby
    have hxt := h.comp i l k g fl fi hg hfl hfi x y t hxy (ye ▸ hyt)
    have eq := (h.elementary i k fi ci A U c X R hfi hci hc ma mx).1.1.1.2 x s t (xe ▸ hxs) hxt
    exact hj.1.1.1.2 t u v (eq ▸ hsu) htv

end YesMetaZFC.SetTheory.LargeCardinal
