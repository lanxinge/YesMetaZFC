import YesMetaZFC.SetTheory.LargeCardinal.RelativeRankAgreement
import YesMetaZFC.Model.SetTheory.Internal.SourcePower
import YesMetaZFC.Model.SetTheory.Internal.SourceCantor

/-! # 共同极限秩段在新源中的实际枚举

严格较早层的原枚举图已经属于共同秩段。新源在自身相对幂集中统一选取这些
枚举，用两个有限列坐标编码层号及层内位置，再在源内构造整层的双射。
-/
namespace YesMetaZFC.SetTheory.LargeCardinal
open Definitional.Project InnerModel Internal
universe u
variable {M : Structure.{u}} (hZF : M.Models ZF)
local notation "I" => kp_pair_l (ZF.modelsKP hZF)

private theorem er_enumeration_l {ω L K X R W : M.Domain}
    (source : Ep_source_d hZF ω L K X R) (power : Sc_power_d X)
    (limit : M.IsLimitOrdinal L) (hW : M.mem W X) (rank : Vr_d X L W)
    (lower : ∀ β, M.mem β L → ∃ U μ f, M.mem U X ∧ Vr_d X β U ∧ M.mem μ L ∧
      M.mem f X ∧ M.IsSetBijectionFromTo I f μ U) :
    ∃ e, M.mem e X ∧ M.IsSetBijectionFromTo I e L W := by
  obtain ⟨c, hc⟩ := source.code
  obtain ⟨B, G, hB, hG, cert⟩ := rank
  have rank : Vr_d X L W := ⟨B, G, hB, hG, cert⟩
  have gf := (cert W hW).2.1
  have stage β U (hβ : M.mem β L) (hu : Rd_entry_d β U G) : Vr_d X β U :=
    sc_rank_stage_l hZF source.omega source.transitive hc source.theory hW hB hG cert hβ hu
  have inside β U (hu : Rd_entry_d β U G) : M.mem U W :=
    ((cert U (source.transitive B hB U (gf.bound_l hu).2)).2.2.2).mpr
      ⟨β, (gf.bound_l hu).1, U, (gf.bound_l hu).2, hu, fun _ h => h⟩
  obtain ⟨Q, hQ, product⟩ := source.theory.algebra.product L W source.cardinal_mem hW
  obtain ⟨C, hC, subsets⟩ := power Q hQ
  let ρ : Env M 3 := ⟨Fin.cases W (Fin.cases G (fun _ => L)), fun _ => L⟩
  let φ : BinarySchema 3 := {
    body := Formula.existsMem (.bound 2) (.conj (rd_entry0_m (.bound 2) .newest (.bound 4))
      (Formula.existsMem (.bound 5) (sh_bijection_m (.bound 2) .newest (.bound 1)))) }
  have read β f : φ.denote ρ β f ↔ ∃ U, M.mem U W ∧ Rd_entry_d β U G ∧
      ∃ μ, M.mem μ L ∧ M.IsSetBijectionFromTo I f μ U := by
    simp only [φ, BinarySchema.denote, Formula.satisfies_existsMem_iff, Formula.satisfies_conj_iff,
      rd_entry0_sat_l hZF.1, sh_bijection_sat_l (ZF.modelsKP hZF)]; rfl
  obtain ⟨H, hH, hf, select⟩ := sc_uniform_source_l hZF source.omega source.transitive hc source.theory φ
    (.existsMem _ (.conj (rd_entry0_delta_l ..) (.existsMem _ (sh_bijection_delta_l ..))))
    ρ (Fin.cases hW (Fin.cases hG (fun _ => source.cardinal_mem))) source.cardinal_mem hC (fun β hβ => by
      obtain ⟨U, hU, hu⟩ := gf.2.1 β hβ
      obtain ⟨U', μ, f, hU', rank', hμ, hfx, bij⟩ := lower β hβ
      have eq := rank'.unique_l hZF source.transitive hU' (source.transitive B hB U hU) (stage β U hβ hu)
      subst U'
      have uw := inside β U hu
      have sub := (rank.transitive_l hZF source.transitive hW) U uw
      exact ⟨f, (subsets f).mpr ⟨hfx, fun p hp => by
        obtain ⟨a, ha, b, hb, pair⟩ := (fn0_of_function_l (ZF.modelsKP hZF) bij.1.1).1 p hp
        exact (product p).mpr ⟨a, limit.1.transitive μ hμ a ha, b, sub b hb, pair⟩⟩,
        (read β f).mpr ⟨U, uw, hu, μ, hμ, bij⟩⟩)
  have covered x (hx : M.mem x W) : ∃ β m f, M.mem β L ∧ M.mem m L ∧ M.mem f C ∧
      Rd_entry_d β f H ∧ Rd_entry_d m x f := by
    obtain ⟨β, U, hβ, hU, hu, hxU⟩ := sc_rank_limit_l hZF source.omega source.transitive hc source.theory hW rank limit hx
    obtain ⟨f, hfc, hβf⟩ := hf.2.1 β hβ
    obtain ⟨U', hU', hg, μ, hμ, bij⟩ := (read β f).mp (select β f hβf)
    have eq := hu.unique_l hZF source.transitive hU (source.transitive W hW U' hU') (stage β U' hβ hg)
    subst U'
    obtain ⟨m, hm, hmx⟩ := bij.2 x hxU
    exact ⟨β, m, f, hβ, limit.1.transitive μ hμ m hm, hfc, hβf, hmx⟩
  obtain ⟨q, hq, qi⟩ := source.finite_index_l hZF limit.1
  obtain ⟨z, hz, hzω⟩ := source.omega.1.1
  obtain ⟨o, ho, hoω⟩ := source.omega.1.2 z hzω
  obtain ⟨t, ht, htω⟩ := source.omega.1.2 o hoω
  have hzo : z ≠ o := fun eq => hz z (eq ▸ ho.predecessor_mem)
  let η : Env M 7 := ⟨Fin.cases L (Fin.cases C (Fin.cases K (Fin.cases H
    (Fin.cases z (Fin.cases o (fun _ => q)))))), fun _ => L⟩
  let ψ : BinarySchema 7 := {
    body := Formula.existsMem (.bound 2) (Formula.existsMem (.bound 3)
      (Formula.existsMem (.bound 5) (Formula.existsMem (.bound 7)
      (.conj (rd_entry0_m (.bound 3) (.bound 1) (.bound 9))
        (.conj (rd_entry0_m (.bound 10) (.bound 3) .newest)
          (.conj (rd_entry0_m (.bound 11) (.bound 2) .newest)
            (.conj (rd_entry0_m (.bound 2) (.bound 5) (.bound 1))
              (rd_entry0_m .newest (.bound 4) (.bound 12))))))))) }
  have decode x i : ψ.denote η x i ↔ ∃ β, M.mem β L ∧ ∃ m, M.mem m L ∧
      ∃ f, M.mem f C ∧ ∃ s, M.mem s K ∧ Rd_entry_d β f H ∧ Rd_entry_d z β s ∧
        Rd_entry_d o m s ∧ Rd_entry_d m x f ∧ Rd_entry_d s i q := by
    simp only [ψ, BinarySchema.denote, Formula.satisfies_existsMem_iff, Formula.satisfies_conj_iff,
      rd_entry0_sat_l hZF.1]; rfl
  obtain ⟨e, he, ef, es⟩ := sc_uniform_source_l hZF source.omega source.transitive hc source.theory ψ
    (.existsMem _ (.existsMem _ (.existsMem _ (.existsMem _ (.conj (rd_entry0_delta_l ..)
      (.conj (rd_entry0_delta_l ..) (.conj (rd_entry0_delta_l ..)
        (.conj (rd_entry0_delta_l ..) (rd_entry0_delta_l ..))))))))) η
    (Fin.cases source.cardinal_mem (Fin.cases hC (Fin.cases source.finite_mem (Fin.cases hH
      (Fin.cases (source.transitive ω source.omega_mem z hzω)
        (Fin.cases (source.transitive ω source.omega_mem o hoω) (fun _ => hq))))))) hW source.cardinal_mem (fun x hx => by
      obtain ⟨β, m, f, hβ, hm, hfc, hβf, hmx⟩ := covered x hx
      obtain ⟨s, sf, sz, so⟩ := ep_two_values_l hZF hzo
        ((ht z).mpr (Or.inl ho.predecessor_mem)) ht.predecessor_mem hβ hm
      have hs := (source.finite s).mpr ⟨t, htω, fn0_function_l (ZF.modelsKP hZF) sf⟩
      obtain ⟨i, hi, hsi⟩ := qi.1.2.2 s hs
      exact ⟨i, hi, (decode x i).mpr ⟨β, hβ, m, hm, f, hfc, s, hs, hβf, sz, so, hmx, hsi⟩⟩)
  have inj : M.IsSetInjectionFromTo I e W L := by
    refine ⟨fn0_function_l (ZF.modelsKP hZF) ef, fun x y i hxi hyi => ?_⟩
    obtain ⟨β, _, m, _, f, _, s, hs, hβf, sz, so, hmx, hsi⟩ := (decode x i).mp (es x i hxi)
    obtain ⟨β', _, m', _, f', _, s', _, hβf', sz', so', hmy, hsi'⟩ := (decode y i).mp (es y i hyi)
    have eq := qi.2 s' s i hsi' hsi
    subst s'
    obtain ⟨_, _, sf⟩ := (source.finite s).mp hs
    have eq := sf.1.2 z β' β sz' sz
    subst β'
    have eq := sf.1.2 o m' m so' so
    subst m'
    have eq := (fn0_function_l (ZF.modelsKP hZF) hf).1.2 β f' f hβf' hβf
    subst f'
    obtain ⟨_, _, _, _, _, bij⟩ := (read β f).mp (select β f hβf)
    exact bij.1.1.1.2 m x y hmx hmy
  let equal : BinarySchema 0 := { body := Formula.extensionalEq (.bound 1) .newest }
  let ε : Env M 0 := ⟨Fin.elim0, fun _ => L⟩
  have eqs a b : equal.denote ε a b ↔ a = b := Formula.satisfies_extensionalEq_iff_eq hZF.1 ..
  obtain ⟨i, hi, fi, is⟩ := sc_uniform_source_l hZF source.omega source.transitive hc source.theory equal (.atom ..)
    ε (fun k => Fin.elim0 k) source.cardinal_mem hW
    (fun a ha => ⟨a, rank.ordinal_subset_l hZF source.transitive hW a ha, (eqs a a).mpr rfl⟩)
  exact sc_cantor_bernstein_l hZF source.omega source.transitive hc source.theory source.cardinal_mem hW hi he
    ⟨fn0_function_l (ZF.modelsKP hZF) fi, fun a b x ha hb =>
      ((eqs a x).mp (is a x ha)).trans ((eqs b x).mp (is b x hb)).symm⟩ inj

theorem ea_rank_size_l {ω L K X R Y W : M.Domain}
    (target : Ep_source_d hZF ω L K X R) (power : Sc_power_d X) (hierarchy : Sc_hierarchy_d X)
    (hY : M.TransitiveSet Y) (limit : M.IsLimitOrdinal L) (hWX : M.mem W X) (hWY : M.mem W Y)
    (rank : Vr_d X L W) (rank' : Vr_d Y L W) (sizes : Sc_rank_size_d I Y L) : Sc_rank_size_d I X L := by
  have lower β (hβ : M.mem β L) : ∃ U μ f, M.mem U X ∧ Vr_d X β U ∧ M.mem μ L ∧
      M.mem f X ∧ M.IsSetBijectionFromTo I f μ U := by
    obtain ⟨U, μ, f, hU, hu, hμ, hf, bij⟩ := sizes.lower β hβ
    obtain ⟨V, hV, hv⟩ := hierarchy β (target.transitive L target.cardinal_mem β hβ) (limit.1.mem hβ)
    have βW := rank.ordinal_subset_l hZF target.transitive hWX β hβ
    obtain ⟨hUW, huW⟩ := rank'.rank_l hZF hY hWY limit βW hU hu
    obtain ⟨hVW, hvW⟩ := rank.rank_l hZF target.transitive hWX limit βW hV hv
    have eq := huW.unique_l hZF (rank.transitive_l hZF target.transitive hWX) hUW hVW hvW
    subst V
    have hfW := rank'.relation_mem_l hZF hY hWY limit
      (rank.ordinal_subset_l hZF target.transitive hWX μ hμ) hUW hf (fn0_of_function_l (ZF.modelsKP hZF) bij.1.1).1
    exact ⟨U, μ, f, hV, hv, hμ, target.transitive W hWX f hfW, bij⟩
  obtain ⟨e, he, bij⟩ := er_enumeration_l hZF target power limit hWX rank lower
  exact ⟨⟨W, e, hWX, rank, he, bij⟩, lower⟩

end YesMetaZFC.SetTheory.LargeCardinal
