import YesMetaZFC.SetTheory.LargeCardinal.IterationColumnPull
import YesMetaZFC.SetTheory.LargeCardinal.IterationOwnerPull
import YesMetaZFC.SetTheory.LargeCardinal.IterationUltraPull
import YesMetaZFC.SetTheory.LargeCardinal.ExtenderLocalRead
import YesMetaZFC.SetTheory.LargeCardinal.ExtenderStrengthAgreement

/-! # 原 nice 树沿反射壳整体回拉

全初等边列先已恢复；所属判断和最大强度分别由模型限制与有界证书反射。
每条指定超幂使用原公式的有限反射，商、塌缩和边图均保持原值。
-/
namespace YesMetaZFC.SetTheory.LargeCardinal
open Definitional.Project InnerModel Internal
universe u
variable {M : Structure.{u}} (hZFC : M.Models ZFC)
local notation "hZF" => ZFC.models_zf_l hZFC
local notation "I" => kp_pair_l (ZF.modelsKP hZF)

theorem it_nice_pull_l {ω B R b K U S u J C V π c c' T Q Q' G G' E E' L L' : M.Domain}
    (sb : Ep_source_d hZF ω ω K B R) (su : Ep_source_d hZF ω ω J U S)
    (mb : Smem_d I b B R) (mu : Smem_d I u U S) (hj : Smap_d I ω b u B U π)
    (hC : M.mem C B) (fs : Fs_read_d ω C) (vt : M.TransitiveSet V) (hCV : Rd_entry_d C V π)
    (hQ : M.mem Q C) (hG : M.mem G C) (hE : M.mem E C) (hL : M.mem L C)
    (hcc : Rd_entry_d c c' π) (hTT : Rd_entry_d T T π) (hQQ : Rd_entry_d Q Q' π)
    (hGG : Rd_entry_d G G' π) (hEE : Rd_entry_d E E' π) (hLL : Rd_entry_d L L' π)
    (diagram : It_diagram_d hZF ω ω T Q G) (big : It_nice_d hZF ω c' ω T Q' G' E' L')
    (powers : ∀ i a Y W, Rd_entry_d i a Q' → Smem_d I a Y W → Sc_power_d Y)
    (reflect : Lr_reflect_d (it_ultra_m (d := 7) (.bound 6) (.bound 5) (.bound 4) (.bound 3) (.bound 2) (.bound 1) (.bound 0)) V) :
    It_nice_d hZF ω c ω T Q G E L := by
  have hw := sb.omega
  have cb := sb.transitive C hC
  have nat := hj.natural_l hZF hw sb.transitive su.transitive mb mu sb.omega_mem
  have omega := hj.omega_l I hZF hw sb.transitive su.transitive mb mu sb.omega_mem
  -- 内部 ω 上的每一步都有操作；因此操作列及支撑列均保持完整定义域。
  have ed i : (∃ p, Rd_entry_d i p E') ↔ M.mem i ω := (big.tree.move_domain i).trans
    ⟨fun ⟨j, hj, sj⟩ => hw.transitive hZF j hj i sj.predecessor_mem,
      fun hi => (hw.1.2 i hi).imp fun j h => ⟨h.2, h.1⟩⟩
  have ld i : (∃ ρ, Rd_entry_d i ρ L') ↔ M.mem i ω := by
    constructor
    · rintro ⟨ρ, hρ⟩
      obtain ⟨p, _, _, hp, _⟩ := (big.levels i ρ).mp hρ
      exact (ed i).mp ⟨p, hp⟩
    · intro hi
      obtain ⟨p, hp⟩ := (ed i).mpr hi
      obtain ⟨κ, ρ, F, pay⟩ := big.active i p hp
      exact ⟨ρ, (big.levels i ρ).mpr ⟨p, κ, F, hp, pay⟩⟩
  have qf := hj.column_l hZF hw sb.transitive su.transitive vt mb mu hCV omega hQQ hQ
    big.tree.diagram.model_function big.tree.diagram.model_domain
  have gf := hj.column_l hZF hw sb.transitive su.transitive vt mb mu hCV hTT hGG hG
    big.tree.diagram.map_function big.tree.diagram.map_domain
  have ef := hj.column_l hZF hw sb.transitive su.transitive vt mb mu hCV omega hEE hE big.tree.move_function (fun i => (ed i).symm)
  have lf := hj.column_l hZF hw sb.transitive su.transitive vt mb mu hCV omega hLL hL big.function (fun i => (ld i).symm)
  have read {D f g i i' y} (ff : Fn0_d D C f) (gg : M.IsSetFunction I g) (hfg : Rd_entry_d f g π)
      (hi : Rd_entry_d i i' π) (hiD : M.mem i D) (hy : Rd_entry_d i' y g) :=
    hj.entry_preimage_l hZF hw sb.transitive su.transitive mb mu cb ff gg hfg hi hiD hy
  have image {f g i p} (ff : Fn0_d ω C f) (hfg : Rd_entry_d f g π) (hp : Rd_entry_d i p f) :
      ∃ p', Rd_entry_d i p' g ∧ Rd_entry_d p p' π := by
    obtain ⟨p', _, hpp⟩ := hj.1.1.2.2 p (cb p (ff.bound_l hp).2)
    exact ⟨p', (hj.entry_l hZF hw sb.transitive su.transitive mb mu (nat i (ff.bound_l hp).1) hpp hfg).mp hp, hpp⟩
  have payload {i p p' κ ρ F} (hp : Rd_entry_d i p' E') (hpp : Rd_entry_d p p' π) (pay : It_payload_d p κ ρ F) :
      ∃ κ' ρ' F', It_payload_d p' κ' ρ' F' ∧ Rd_entry_d κ κ' π ∧ Rd_entry_d ρ ρ' π ∧ Rd_entry_d F F' π := by
    obtain ⟨κ', ρ', F', pay'⟩ := big.active i p' hp
    obtain ⟨κ₀, ρ₀, F₀, pay₀, hk, hl, hf⟩ := it_payload_pull_l hZF hw sb.transitive su.transitive mb mu hj hpp pay'
    obtain ⟨rfl, rfl, rfl⟩ := pay.unique_l pay₀
    exact ⟨κ', ρ', F', pay', hk, hl, hf⟩
  have model {i a a' Y W} (ha : Rd_entry_d i a' Q') (haa : Rd_entry_d a a' π) (my : Smem_d I a' Y W) :
      ∃ X P H σ, Smem_d I a X P ∧ Ep_source_d hZF ω ω H X P ∧ Rd_entry_d X Y π ∧
        M.IsRestrictionOf I σ π X ∧ Smap_d I ω a a' X Y σ ∧ Sc_power_d X := by
    obtain ⟨Y₀, W₀, N, my₀, sy⟩ := big.tree.sources i a' ha
    obtain ⟨ey, ew⟩ := smdl_unique_l I my₀.1 my.1
    subst Y₀ W₀
    obtain ⟨X, P, H, σ, mx, sx, hXY, res, hs⟩ := ep_set_source_pull_l hZF sb su mb mu hj haa my sy
    exact ⟨X, P, H, σ, mx, sx, hXY, res, hs,
      (sc_power_iff_l hZF hw sx.transitive sy.transitive mx my hs).mpr (powers i a' Y W ha my)⟩
  have sources i a (ha : Rd_entry_d i a Q) : It_source_d hZF ω a := by
    obtain ⟨a', ha', haa⟩ := image qf hQQ ha
    obtain ⟨Y, W, _, my, _⟩ := big.tree.sources i a' ha'
    obtain ⟨X, P, H, _, mx, sx, _⟩ := model ha' haa my
    exact ⟨X, P, H, mx, sx⟩
  refine ⟨⟨⟨hw, diagram, ?_, sources, (fn0_function_l (ZF.modelsKP hZF) ef).1, ?_, ?_, ?_⟩,
    (fn0_function_l (ZF.modelsKP hZF) lf).1, ?_, ?_, ?_⟩, ?_⟩
  · intro o ho
    have hoω := (big.tree.diagram.model_domain o).mpr ⟨c', big.tree.root o ho⟩
    obtain ⟨a, _, ha, haa⟩ := read qf big.tree.diagram.model_function hQQ (nat o hoω) hoω (big.tree.root o ho)
    exact (hj.1.2 a c c' haa hcc) ▸ ha
  · intro i
    exact ((fn0_function_l (ZF.modelsKP hZF) ef).2.1 i).symm.trans ((ed i).symm.trans (big.tree.move_domain i))
  · intro i j hjω succ
    -- 读取原前驱及各列中的指定条目，保持原树边与超幂。
    have hi := hw.transitive hZF j hjω i succ.predecessor_mem
    obtain ⟨k, a', d', b', g', p', κ', ρ', F', Y, W, Z, H, pred, ha', hd', hb', hg', hp', pay', my, mz, loc', agree', ultra', _⟩ := big.step_l hZF hjω succ
    have hk := hw.transitive hZF j hjω k pred.1
    obtain ⟨a, _, ha, haa⟩ := read qf big.tree.diagram.model_function hQQ (nat i hi) hi ha'
    obtain ⟨d, hdC, hd, hdd⟩ := read qf big.tree.diagram.model_function hQQ (nat k hk) hk hd'
    obtain ⟨e, heC, he, hee⟩ := read qf big.tree.diagram.model_function hQQ (nat j hjω) hjω hb'
    obtain ⟨p, hpC, hp, hpp⟩ := read ef big.tree.move_function hEE (nat i hi) hi hp'
    obtain ⟨r, pair, hr⟩ := hg'
    have hrT := (big.tree.diagram.map_domain r).mpr ⟨g', hr⟩
    have fixed := hj.fixed_pair_l hZF hw sb.transitive su.transitive mb mu
      (sb.transitive T (hj.1.1.input_mem_of_pairMember hTT) r hrT) pair (nat k hk) (nat j hjω)
    obtain ⟨g, hgC, hg, hgg⟩ := read gf big.tree.diagram.map_function hGG fixed hrT hr
    obtain ⟨κ, ρ, F, pay, hκ, hρ, hF⟩ := it_payload_pull_l hZF hw sb.transitive su.transitive mb mu hj hpp pay'
    obtain ⟨X, P, K₀, σ, mx, sx, hXY, res, hs, power⟩ := model ha' haa my
    obtain ⟨N, O, K₁, τ, mn, sn, hNZ, _, _, _⟩ := model hd' hdd mz
    have lift {x y} (hxy : Rd_entry_d x y π) (hy : M.mem y Y) :=
      (res.2 x y).mpr ⟨(hj.member_l I hZF hw mb mu hxy hXY).mpr hy, hxy⟩
    have loc := loc'.pull_l hZF hw mx my hs (lift omega loc'.1) (lift hκ loc'.2.1)
      (lift hρ loc'.2.2.1) (lift hF loc'.2.2.2.1)
    have agree := agree'.pull_l hZF hw (sb.read_source_l hZF) (su.read_source_l hZF) mb mu hj hκ hXY hNZ
    have ko := (loc.ordinals_l (ZF.modelsKP hZF) sx.transitive).1
    obtain ⟨K₂, owner⟩ := sx.rebase_l hZF loc.2.1
      (by obtain ⟨_, _, _, _, pre⟩ := loc
          simp only [ex_short_m, ex_pre_m, Formula.satisfies_conj_iff, Formula.satisfies_mem_iff] at pre
          exact ko.transitive ω pre.1.2.2.1)
      (sc_ordinal_small_l hZF hw sx.transitive mx sx.theory loc.2.1 ko)
    obtain ⟨K₃, parent⟩ := agree.subset_l.alphabet_l hZF owner sn ko
    obtain ⟨P₀, hP₀, pool⟩ := power K₂ owner.finite_mem
    have family := (loc.measures_l hZF owner hP₀ pool).transfer_l agree
    have coherent := (loc.coherent_l hZF owner).transfer_l hZF agree
    -- 真实有限幂一致性给出小施加源的族与相干性，再读取原超幂证书。
    obtain ⟨t, pt, tf⟩ := pay
    have kp := pt.mem_l M fs.transitive hpC
    have lp := tf.mem_l M fs.transitive kp.2
    let nc : Nonempty {x // M.mem x C} := ⟨⟨ω, fs.omega_mem⟩⟩
    let η : Env (rt_model_l C nc) 7 := ⟨Fin.cases ⟨g, hgC⟩ (Fin.cases ⟨e, heC⟩ (Fin.cases ⟨d, hdC⟩
      (Fin.cases ⟨F, lp.2⟩ (Fin.cases ⟨ρ, lp.1⟩ (Fin.cases ⟨κ, kp.1⟩ (fun _ => ⟨ω, fs.omega_mem⟩)))))), fun _ => ⟨ω, fs.omega_mem⟩⟩
    let η' : Env M 7 := ⟨Fin.cases g' (Fin.cases b' (Fin.cases d' (Fin.cases F' (Fin.cases ρ' (Fin.cases κ' (fun _ => ω)))))), fun _ => ω⟩
    have ultra := it_ultra_pull_l hZFC sb.transitive su.transitive mb mu hj fs nc hCV reflect η η' rfl
      (Fin.cases hgg (Fin.cases hee (Fin.cases hdd (Fin.cases hF (Fin.cases hρ (Fin.cases hκ (fun _ => omega))))))) parent mn family coherent ultra'
    exact ⟨k, a, d, e, g, p, pred, ha, hd, he, ⟨r, pair, hg⟩, hp,
      Or.inr ⟨κ, ρ, F, X, P, N, O, ⟨t, pt, tf⟩, mx, mn, loc, agree, ultra⟩⟩
  · intro δ hδ limit
    obtain ⟨i, hi, succ⟩ := hw.exists_predecessor_of_mem_of_nonempty hZF hδ limit.2.1
    exact (it_successor_not_limit_l hZF.1 (hw.members_areOrdinals hZF i hi) succ limit).elim
  · intro i ρ
    constructor
    · intro hl
      obtain ⟨ρ', hl', hρ⟩ := image lf hLL hl
      obtain ⟨p', κ', F', hp', pay'⟩ := (big.levels i ρ').mp hl'
      obtain ⟨p, _, hp, hpp⟩ := read ef big.tree.move_function hEE (nat i (lf.bound_l hl).1) (lf.bound_l hl).1 hp'
      obtain ⟨κ, ρ₀, F, pay, _, hρ₀, _⟩ := it_payload_pull_l hZF hw sb.transitive su.transitive mb mu hj hpp pay'
      exact ⟨p, κ, F, hp, (hj.1.2 ρ₀ ρ ρ' hρ₀ hρ) ▸ pay⟩
    · rintro ⟨p, κ, F, hp, pay⟩
      obtain ⟨p', hp', hpp⟩ := image ef hEE hp
      obtain ⟨κ', ρ', F', pay', _, hρ, _⟩ := payload hp' hpp pay
      obtain ⟨ρ₀, _, hl, hρ₀⟩ := read lf big.function hLL (nat i (ef.bound_l hp).1) (ef.bound_l hp).1
        ((big.levels i ρ').mpr ⟨p', κ', F', hp', pay'⟩)
      exact (hj.1.2 ρ₀ ρ ρ' hρ₀ hρ) ▸ hl
  · intro i p κ ρ F a X P hp pay ha mx
    obtain ⟨p', hp', hpp⟩ := image ef hEE hp
    obtain ⟨κ', ρ', F', pay', hκ, hρ, hF⟩ := payload hp' hpp pay
    obtain ⟨a', ha', haa⟩ := image qf hQQ ha
    obtain ⟨Y, W, _, my, _⟩ := big.tree.sources i a' ha'
    obtain ⟨X₀, P₀, H, σ, mx₀, sx, hXY, res, hs, _⟩ := model ha' haa my
    obtain ⟨rfl, rfl⟩ := smdl_unique_l I mx₀.1 mx.1
    obtain ⟨strength, inaccessible⟩ := big.exactness i p' κ' ρ' F' a' Y W hp' pay' ha' my
    exact ⟨strength.pull_l hZF sb.transitive su.transitive mb mu hj su.theory sb.omega_mem sx hXY hκ hρ hF,
      inaccessible.pull_l hZF hw mx my hs ((res.2 ω ω).mpr ⟨sx.omega_mem, omega⟩)
        ((res.2 ρ ρ').mpr ⟨(hj.member_l I hZF hw mb mu hρ hXY).mpr inaccessible.2.1, hρ⟩)⟩
  · intro i j ρ φ hi hj' hij
    obtain ⟨ρ', hi', hρ⟩ := image lf hLL hi
    obtain ⟨φ', hj', hφ⟩ := image lf hLL hj'
    exact (hj.member_l I hZF hw mb mu hρ hφ).mpr (big.increasing i j ρ' φ' hi' hj' hij)
  · intro i p hp
    obtain ⟨p', hp', hpp⟩ := image ef hEE hp
    obtain ⟨κ', ρ', F', pay⟩ := big.active i p' hp'
    obtain ⟨κ, ρ, F, pay, _⟩ := it_payload_pull_l hZF hw sb.transitive su.transitive mb mu hj hpp pay
    exact ⟨κ, ρ, F, pay⟩

end YesMetaZFC.SetTheory.LargeCardinal
