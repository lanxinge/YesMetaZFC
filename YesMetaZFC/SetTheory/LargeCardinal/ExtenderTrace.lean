import YesMetaZFC.SetTheory.LargeCardinal.ExtenderBoundedNodes

/-! # 所属源内的完整支撑迹

只用原测度、代表函数及有限坐标作有界分离。保留实际分离集和计算数据，
以便沿所属源的嵌入搬运后，在原超幂与复制超幂中读取同一个集合。
-/
namespace YesMetaZFC.SetTheory.LargeCardinal
open Definitional.Project InnerModel Internal
universe u
variable {M : Structure.{u}}

def Eb_trace_d (ω κ L K X F m D E a f Z : M.Domain) : Prop := ∃ B J U R ι T,
  M.mem B X ∧ M.mem J X ∧ M.mem U X ∧ M.mem R X ∧ M.mem ι X ∧ M.mem T X ∧
    M.MemberSubset K B ∧ (∀ s, M.mem s J ↔ Ei_d ω L s) ∧
    Rd_fun_d .range F F F U ∧ Rd_fun_d .mem B B B R ∧ Fn0_d D B f ∧ Fn0_d E E ι ∧
    (∀ s, M.mem s E → Rd_entry_d s s ι) ∧
    (∀ t, M.mem t T ↔ ∃ n, M.mem n ω ∧ Fn0_d n L t) ∧ M.MemberSubset Z T ∧
    ∀ t, M.mem t T → (M.mem t Z ↔ Fn0_d m L t ∧ Eb_edge_d ω κ L B J K U R F t ι a f)

variable (hZF : M.Models ZF)
local notation "I" => kp_pair_l (ZF.modelsKP hZF)

theorem eb_trace_l {ω κ K L X R F J m D E a f : M.Domain}
    (source : Ep_source_d hZF ω κ K X R) (hL : M.mem L X) (hF : M.mem F X)
    (indices : ∀ s, M.mem s J ↔ Ei_d ω L s) (ha : M.mem a J)
    (hm : M.mem m ω) (hE : Ep_space_d κ m E) (hfX : M.mem f X) (ff : Fn0_d D X f) :
    ∃ Z, M.mem Z X ∧ Eb_trace_d ω κ L K X F m D E a f Z := by
  obtain ⟨c, code⟩ := source.code
  have hJ := ep_indices_mem_l hZF source hL indices
  have haX := source.transitive J hJ a ha
  obtain ⟨P, hP, coords⟩ := source.theory.algebra.envelope_l hfX
  obtain ⟨Q, hQ, pair⟩ := source.theory.algebra.pair P K hP source.finite_mem
  obtain ⟨B, hB, union⟩ := source.theory.algebra.union Q hQ
  have pb x (hx : M.mem x P) : M.mem x B := (union x).mpr ⟨P, (pair P).mpr (Or.inl rfl), hx⟩
  have kb x (hx : M.mem x K) : M.mem x B := (union x).mpr ⟨K, (pair K).mpr (Or.inr rfl), hx⟩
  have fb : Fn0_d D B f := ff.retarget_l (fun s x hsx => pb x (coords s x hsx).2)
  let membership : BinarySchema 0 := { body := .mem (.bound 1) .newest }
  obtain ⟨R₀, hR₀, shape, rel⟩ := sc_relation_source_l hZF source.omega source.transitive code source.theory membership (.mem ..)
    ⟨Fin.elim0, fun _ => B⟩ (fun i => Fin.elim0 i) hB hB
  have relation x y : Rd_entry_d x y R₀ ↔ M.mem x B ∧ M.mem y B ∧ M.mem x y :=
    (rel x y).trans (and_congr_right fun _ => and_congr_right fun _ => Formula.satisfies_mem_iff ..)
  have membership₀ : Rd_fun_d .mem B B B R₀ := by
    intro p
    refine ⟨fun hp => ?_, ?_⟩
    · obtain ⟨x, y, pair⟩ := shape p hp
      obtain ⟨hx, hy, hxy⟩ := (relation x y).mp ⟨p, pair, hp⟩
      exact ⟨x, y, hx, hy, hxy, pair⟩
    · rintro ⟨x, y, hx, hy, hxy, pair⟩
      obtain ⟨q, qp, hq⟩ := (relation x y).mpr ⟨hx, hy, hxy⟩
      exact kpair_unique_l M hZF.1 qp pair ▸ hq
  obtain ⟨U, hU, range⟩ := sc_range_source_l hZF source.omega source.transitive code source.theory hF
  let equal : BinarySchema 0 := { body := Formula.extensionalEq .newest (.bound 1) }
  let ε : Env M 0 := ⟨Fin.elim0, fun _ => E⟩
  have eqs u x : equal.denote ε u x ↔ x = u := Formula.satisfies_extensionalEq_iff_eq hZF.1 ..
  have hEX := source.space_mem_l hZF hm hE
  obtain ⟨ι, hι, fi, is⟩ := sc_uniform_source_l hZF source.omega source.transitive code source.theory equal (.atom ..) ε
    (fun i => Fin.elim0 i) hEX hEX (fun u hu => ⟨u, hu, (eqs u u).mpr rfl⟩)
  obtain ⟨T, hT, seq⟩ := source.sequences.space L hL
  let ρ : Env M 13 := ⟨Fin.cases m (Fin.cases f (Fin.cases a (Fin.cases ι (Fin.cases F (Fin.cases R₀ (Fin.cases U
    (Fin.cases K (Fin.cases J (Fin.cases B (Fin.cases L (Fin.cases κ (fun _ => ω)))))))))))), fun _ => ω⟩
  let φ : UnarySchema 13 := {
    body := .conj (fn0_m (.bound 1) (.bound 11) .newest)
      (eb_edge_m (.bound 13) (.bound 12) (.bound 11) (.bound 10) (.bound 9) (.bound 8) (.bound 7)
        (.bound 6) (.bound 5) .newest (.bound 4) (.bound 3) (.bound 2)) }
  have sat t : φ.denote ρ t ↔ Fn0_d m L t ∧ Eb_edge_d ω κ L B J K U R₀ F t ι a f :=
    (Formula.satisfies_conj_iff ..).trans (and_congr (fn0_sat_l hZF.1 ..) (eb_edge_sat_l hZF.1 ..))
  obtain ⟨Z, hZ, spec⟩ := sc_separate_source_l I hZF source.omega source.transitive code source.theory φ
    (.conj (fn0_delta_l ..) (eb_edge_delta_l ..)) ρ
    (Fin.cases (source.transitive ω source.omega_mem m hm) (Fin.cases hfX (Fin.cases haX (Fin.cases hι (Fin.cases hF
      (Fin.cases hR₀ (Fin.cases hU (Fin.cases source.finite_mem (Fin.cases hJ (Fin.cases hB (Fin.cases hL
        (Fin.cases source.cardinal_mem (fun _ => source.omega_mem))))))))))))) hT
  refine ⟨Z, hZ, B, J, U, R₀, ι, T, hB, hJ, hU, hR₀, hι, hT, kb, indices, range, membership₀, fb, fi, ?_, ?_,
    (fun t ht => ((spec t).mp ht).1), fun t ht => (spec t).trans ((and_iff_right ht).trans (sat t))⟩
  · intro s hs
    obtain ⟨x, _, hsx⟩ := fi.2.1 s hs
    exact (eqs s x).mp (is s x hsx) ▸ hsx
  · exact fun t => (seq t).trans (exists_congr fun n => and_congr_right fun _ =>
      ⟨fn0_of_function_l (ZF.modelsKP hZF), fn0_function_l (ZF.modelsKP hZF)⟩)

end YesMetaZFC.SetTheory.LargeCardinal
