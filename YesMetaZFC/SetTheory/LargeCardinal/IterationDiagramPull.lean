import YesMetaZFC.SetTheory.LargeCardinal.ExtenderSetPull
import YesMetaZFC.SetTheory.LargeCardinal.IterationTree

/-! # 整棵 ω 树的模型列与全初等嵌入列回拉

自然数及其关系图保持原值。每个模型沿拥有集合上的实际限制回拉完整源；
每条边由两端限制的交换三角形恢复全内部初等性。
-/
namespace YesMetaZFC.SetTheory.LargeCardinal
open Definitional.Project InnerModel Internal
universe u
variable {M : Structure.{u}} (hZF : M.Models ZF)
local notation "I" => kp_pair_l (ZF.modelsKP hZF)

theorem it_diagram_pull_l {ω B R b K U S u J C V π T Q G T' Q' G' : M.Domain}
    (source : Ep_source_d hZF ω ω K B R) (target : Ep_source_d hZF ω ω J U S)
    (mb : Smem_d I b B R) (mu : Smem_d I u U S) (hj : Smap_d I ω b u B U π)
    (hC : M.mem C B) (ct : M.TransitiveSet C) (vt : M.TransitiveSet V)
    (hCV : Rd_entry_d C V π) (hQ : M.mem Q C) (hG : M.mem G C)
    (hTT : Rd_entry_d T T' π) (hQQ : Rd_entry_d Q Q' π) (hGG : Rd_entry_d G G' π)
    (diagram : It_diagram_d hZF ω ω T' Q' G')
    (sources : ∀ i c, Rd_entry_d i c Q' → It_source_d hZF ω c) :
    T = T' ∧ It_diagram_d hZF ω ω T Q G ∧ ∀ i c, Rd_entry_d i c Q → It_source_d hZF ω c := by
  have hw := source.omega
  have nat := hj.natural_l hZF hw source.transitive target.transitive mb mu source.omega_mem
  have omega := hj.omega_l I hZF hw source.transitive target.transitive mb mu source.omega_mem
  have same := hj.relation_preimage_l hZF hw source.transitive target.transitive mb mu omega nat hTT
    ⟨diagram.order.relation, diagram.order.bound⟩
  subst T'
  have ownQ := (hj.member_l I hZF hw mb mu hQQ hCV).mp hQ
  have ownG := (hj.member_l I hZF hw mb mu hGG hCV).mp hG
  have qf : Fn0_d ω C Q := (hj.function_l hZF hw source.transitive target.transitive mb mu omega hCV hQQ).mpr
    (fn0_of_function_l (ZF.modelsKP hZF) ⟨diagram.model_function, diagram.model_domain, fun i hi => by
      obtain ⟨a, ha⟩ := (diagram.model_domain i).mp hi
      exact ⟨a, (rd_entry_transitive_l vt ownQ ha).2, ha⟩⟩)
  have gf : Fn0_d T C G := (hj.function_l hZF hw source.transitive target.transitive mb mu hTT hCV hGG).mpr
    (fn0_of_function_l (ZF.modelsKP hZF) ⟨diagram.map_function, diagram.map_domain, fun i hi => by
      obtain ⟨a, ha⟩ := (diagram.map_domain i).mp hi
      exact ⟨a, (rd_entry_transitive_l vt ownG ha).2, ha⟩⟩)
  have model {i a} (ha : Rd_entry_d i a Q) : ∃ a' X P H Y W N,
      Rd_entry_d i a' Q' ∧ Rd_entry_d a a' π ∧ Smem_d I a X P ∧ Ep_source_d hZF ω ω H X P ∧
      Smem_d I a' Y W ∧ Ep_source_d hZF ω ω N Y W ∧ Rd_entry_d X Y π := by
    obtain ⟨a', _, haa⟩ := hj.1.1.2.2 a (source.transitive C hC a (qf.bound_l ha).2)
    have hi := (hj.entry_l hZF hw source.transitive target.transitive mb mu (nat i (qf.bound_l ha).1) haa hQQ).mp ha
    obtain ⟨Y, W, N, my, sy⟩ := sources i a' hi
    obtain ⟨X, P, H, _, mx, sx, hXY, _⟩ := ep_set_source_pull_l hZF source target mb mu hj haa my sy
    exact ⟨a', X, P, H, Y, W, N, hi, haa, mx, sx, my, sy, hXY⟩
  have ready i a (ha : Rd_entry_d i a Q) : It_source_d hZF ω a := by
    obtain ⟨_, X, P, H, _, _, _, _, _, mx, sx, _⟩ := model ha
    exact ⟨X, P, H, mx, sx⟩
  have edge {i j f} (hf : It_map_d G i j f) : ∃ g, It_map_d G' i j g ∧ Rd_entry_d f g π := by
    obtain ⟨r, pair, hr⟩ := hf
    have rt := (gf.bound_l hr).1
    have ij := diagram.order.bound i j ⟨r, pair, rt⟩
    have fixed := hj.fixed_pair_l hZF hw source.transitive target.transitive mb mu
      (source.transitive T (hj.1.1.input_mem_of_pairMember hTT) r rt) pair (nat i ij.1) (nat j ij.2)
    obtain ⟨g, _, hfg⟩ := hj.1.1.2.2 f (source.transitive C hC f (gf.bound_l hr).2)
    exact ⟨g, ⟨r, pair, (hj.entry_l hZF hw source.transitive target.transitive mb mu fixed hfg hGG).mp hr⟩, hfg⟩
  have owned {i j f} (hf : It_map_d G i j f) : M.mem f C := hf.elim fun _ h => (gf.bound_l h.2).2
  have value {i j f x y} (hf : It_map_d G i j f) (hxy : Rd_entry_d x y f) : M.mem x B ∧ M.mem y B := by
    have xy := rd_entry_transitive_l ct (owned hf) hxy
    exact ⟨source.transitive C hC x xy.1, source.transitive C hC y xy.2⟩
  refine ⟨rfl, ⟨diagram.order, (fn0_function_l (ZF.modelsKP hZF) qf).1,
    (fn0_function_l (ZF.modelsKP hZF) qf).2.1, ?_, (fn0_function_l (ZF.modelsKP hZF) gf).1,
    (fn0_function_l (ZF.modelsKP hZF) gf).2.1, ?_, ?_, ?_⟩, ready⟩
  · intro i a ha
    obtain ⟨X, P, _, mx, _⟩ := ready i a ha
    exact ⟨X, P, mx.1⟩
  · intro i j f a X P d Y W hf ha hd mx my
    obtain ⟨a', X₀, P₀, _, X', P', _, ha', _, ma, _, ma', _, hXX⟩ := model ha
    obtain ⟨d', Y₀, W₀, _, Y', W', _, hd', _, md, _, md', _, hYY⟩ := model hd
    obtain ⟨rfl, rfl⟩ := smdl_unique_l I ma.1 mx
    obtain ⟨rfl, rfl⟩ := smdl_unique_l I md.1 my
    obtain ⟨g, hg, hfg⟩ := edge hf
    exact ep_set_map_pull_l hZF source target mb mu hj ma ma' md md' hXX hYY hfg
      (diagram.elementary i j g a' X' P' d' Y' W' hg ha' hd' ma'.1 md'.1)
  · intro i f hf x y hxy
    obtain ⟨g, hg, hfg⟩ := edge hf
    obtain ⟨x', _, hx⟩ := hj.1.1.2.2 x (value hf hxy).1
    obtain ⟨y', _, hy⟩ := hj.1.1.2.2 y (value hf hxy).2
    have eq := diagram.identity i g hg x' y'
      ((hj.entry_l hZF hw source.transitive target.transitive mb mu hx hy hfg).mp hxy)
    exact hj.1.2 x y y' (eq ▸ hx) hy
  · intro i j k f g h hf hg hh x y z hxy hyz
    obtain ⟨f', hf', ff⟩ := edge hf
    obtain ⟨g', hg', gg⟩ := edge hg
    obtain ⟨h', hh', hh⟩ := edge hh
    obtain ⟨x', _, hx⟩ := hj.1.1.2.2 x (value hf hxy).1
    obtain ⟨y', _, hy⟩ := hj.1.1.2.2 y (value hf hxy).2
    obtain ⟨z', _, hz⟩ := hj.1.1.2.2 z (value hg hyz).2
    exact (hj.entry_l hZF hw source.transitive target.transitive mb mu hx hz hh).mpr
      (diagram.comp i j k f' g' h' hf' hg' hh' x' y' z'
        ((hj.entry_l hZF hw source.transitive target.transitive mb mu hx hy ff).mp hxy)
        ((hj.entry_l hZF hw source.transitive target.transitive mb mu hy hz gg).mp hyz))

end YesMetaZFC.SetTheory.LargeCardinal
