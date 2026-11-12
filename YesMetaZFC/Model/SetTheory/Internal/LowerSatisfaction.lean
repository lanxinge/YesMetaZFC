import YesMetaZFC.Model.SetTheory.Source.ClosureSyntax
import YesMetaZFC.SetTheory.CumulativeClosure
import YesMetaZFC.Model.SetTheory.Types.FlatPredecessor

/-! # 对幂集的原公式相对化

量词直接以 x⊆X 为界，不把 P(X) 当作额外参数。在包含 X 的任意秩层中，
所有这些见证都已存在；因此即使 P(X) 等于整个外层，原公式仍正确读取。
-/
namespace YesMetaZFC.SetTheory.Internal
open Definitional.Project InnerModel
universe u
variable {M : Structure.{u}}

def lp_rel_m : {n d : Nat} → Formula 1 n → Term d → (Fin n → Term d) → Formula 1 d
  | _, _, .falsum, _, _ => .falsum
  | _, _, .truth, _, _ => .truth
  | _, _, .mem s t, _, e => .mem (s.bind e) (t.bind e)
  | _, _, .atom r hr ts, _, e => .atom r hr (ts.bind e)
  | _, _, .neg φ, X, e => .neg (lp_rel_m φ X e)
  | _, _, .conj φ ψ, X, e => .conj (lp_rel_m φ X e) (lp_rel_m ψ X e)
  | _, _, .disj φ ψ, X, e => .disj (lp_rel_m φ X e) (lp_rel_m ψ X e)
  | _, _, .imp φ ψ, X, e => .imp (lp_rel_m φ X e) (lp_rel_m ψ X e)
  | _, _, .iff φ ψ, X, e => .iff (lp_rel_m φ X e) (lp_rel_m ψ X e)
  | _, _, .existsE φ, X, e => .existsE (.conj (Formula.subset .newest X.weaken)
      (lp_rel_m φ X.weaken (Fin.cases .newest (fun i => (e i).weaken))))
  | _, _, .forallE φ, X, e => .forallE (.imp (Formula.subset .newest X.weaken)
      (lp_rel_m φ X.weaken (Fin.cases .newest (fun i => (e i).weaken))))

@[simp] theorem lp_rel_closed_l {n d} (φ : Formula 1 n) (hφ : φ.FreeClosed) (X : Term d) (e : Fin n → Term d)
    (hX : X.freeSupport = []) (he : ∀ i, (e i).freeSupport = []) : (lp_rel_m φ X e).FreeClosed := by
  induction φ generalizing d <;> simp only [Definitional.Formula.FreeClosed] at hφ
  case falsum | truth => simp only [lp_rel_m, Definitional.Formula.FreeClosed]
  case mem s t =>
    exact ⟨(Definitional.Term.freeSupport_bind_of_closed e he s).trans hφ.1,
      (Definitional.Term.freeSupport_bind_of_closed e he t).trans hφ.2⟩
  case atom _ _ ts => exact (Definitional.TermVector.freeClosed_bind_iff_of_closed e he ts).mpr hφ
  case neg φ ih => exact ih hφ X e hX he
  case conj φ ψ ih jh | disj φ ψ ih jh | imp φ ψ ih jh | iff φ ψ ih jh =>
    exact ⟨ih hφ.1 X e hX he, jh hφ.2 X e hX he⟩
  case existsE φ ih | forallE φ ih =>
    exact ⟨(by simp -implicitDefEqProofs [hX]),
      ih hφ X.weaken _ (by simpa using hX) (Fin.cases rfl (fun i => by simpa using he i))⟩

/-- 在实际幂集模型中读取原公式；幂集载体只出现在证明中，不进入生成的公式。 -/
theorem lp_rel_model_l {P : M.Domain} (hp : M.TransitiveSet P) (np : Nonempty {x // M.mem x P})
    {n d} (φ : Formula 1 n) (hc : φ.FreeClosed) (η : Env (rt_model_l P np) n)
    (ρ : Env M d) (X : Term d) (e : Fin n → Term d) (power : M.IsPowerSetOf P (X.eval ρ))
    (he : ∀ i, (e i).eval ρ = (η.bound i).val) :
    Formula.satisfies ρ (lp_rel_m φ X e) ↔ Formula.satisfies η φ := by
  have atom {n d} (φ : Formula 1 n) (hc : φ.FreeClosed) (hd : φ.IsDelta0)
      (η : Env (rt_model_l P np) n) (ρ : Env M d) (e : Fin n → Term d)
      (he : ∀ i, (e i).eval ρ = (η.bound i).val) : Formula.satisfies ρ (φ.bind e) ↔ Formula.satisfies η φ :=
    (Formula.satisfies_bind ρ e φ).trans ((lr_env_congr_l φ hc _
      (image_env_l (M := rt_model_l P np) (N := M) Subtype.val η) he).trans (rt_model_delta_l hp np hd η).symm)
  induction φ generalizing d <;> simp only [Definitional.Formula.FreeClosed] at hc
  case falsum | truth => simp only [lp_rel_m, Formula.satisfies_falsum_iff, Formula.satisfies_truth_iff]
  case mem s t => exact atom (.mem s t) hc (.mem ..) η ρ e he
  case atom r hr ts => exact atom (.atom r hr ts) hc (.atom ..) η ρ e he
  case neg φ ih => exact not_congr (ih hc η ρ X e power he)
  case conj φ ψ ih jh => exact and_congr (ih hc.1 η ρ X e power he) (jh hc.2 η ρ X e power he)
  case disj φ ψ ih jh => exact or_congr (ih hc.1 η ρ X e power he) (jh hc.2 η ρ X e power he)
  case imp φ ψ ih jh => exact imp_congr (ih hc.1 η ρ X e power he) (jh hc.2 η ρ X e power he)
  case iff φ ψ ih jh => exact iff_congr (ih hc.1 η ρ X e power he) (jh hc.2 η ρ X e power he)
  case existsE φ ih | forallE φ ih =>
    have step (x : (rt_model_l P np).Domain) := ih hc (η.push x) (ρ.push x.val) X.weaken
      (Fin.cases .newest (fun i => (e i).weaken)) (by simpa only [Definitional.Term.eval_weaken] using power)
      (Fin.cases rfl (fun i => (Definitional.Term.eval_weaken ρ x.val (e i)).trans (he i)))
    simp only [lp_rel_m, Formula.satisfies_exists_iff, Formula.satisfies_forall_iff,
      Formula.satisfies_conj_iff, Formula.satisfies_imp_iff, Formula.satisfies_subset_iff,
      Definitional.Term.eval_newest, Definitional.Term.eval_weaken]
    first
    | exact ⟨fun ⟨x, hx, hh⟩ => ⟨⟨x, (power x).mpr hx⟩, (step _).mp hh⟩,
        fun ⟨x, hh⟩ => ⟨x.val, (power x.val).mp x.property, (step x).mpr hh⟩⟩
    | exact ⟨fun h x => (step x).mp (h x.val ((power x.val).mp x.property)),
        fun h x hx => (step ⟨x, (power x).mpr hx⟩).mpr (h _)⟩
/-- 只需当前传递源拥有 X 的全部子集；该条件在每个包含 X 的秩层中自动成立。 -/
theorem lp_rel_absolute_l {Y : M.Domain} (hY : M.TransitiveSet Y) (ny : Nonempty {x // M.mem x Y})
    {n d} (φ : Formula 1 n) (ρ : Env (rt_model_l Y ny) d) (X : Term d) (e : Fin n → Term d)
    (closed : ∀ x, M.MemberSubset x (X.eval ρ).val → M.mem x Y) :
    Formula.satisfies ρ (lp_rel_m φ X e) ↔
      Formula.satisfies (image_env_l (M := rt_model_l Y ny) (N := M) Subtype.val ρ) (lp_rel_m φ X e) := by
  induction φ generalizing d with
  | falsum => exact rt_model_delta_l hY ny .falsum ρ
  | truth => exact rt_model_delta_l hY ny .truth ρ
  | mem _ _ => exact rt_model_delta_l hY ny (.mem ..) ρ
  | atom _ _ _ => exact rt_model_delta_l hY ny (.atom ..) ρ
  | neg φ ih => exact not_congr (ih ρ X e closed)
  | conj φ ψ ih jh => exact and_congr (ih ρ X e closed) (jh ρ X e closed)
  | disj φ ψ ih jh => exact or_congr (ih ρ X e closed) (jh ρ X e closed)
  | imp φ ψ ih jh => exact imp_congr (ih ρ X e closed) (jh ρ X e closed)
  | iff φ ψ ih jh => exact iff_congr (ih ρ X e closed) (jh ρ X e closed)
  | existsE φ ih | forallE φ ih =>
    have sub (x : (rt_model_l Y ny).Domain) : (rt_model_l Y ny).MemberSubset x (X.eval ρ) ↔
        M.MemberSubset x.val (X.eval ρ).val :=
      ⟨fun h a ha => h ⟨a, hY x.val x.property a ha⟩ ha, fun h a ha => h a.val ha⟩
    have step (x : (rt_model_l Y ny).Domain) :
        Formula.satisfies (ρ.push x) (lp_rel_m φ X.weaken (Fin.cases .newest (fun i => (e i).weaken))) ↔
        Formula.satisfies ((image_env_l (M := rt_model_l Y ny) (N := M) Subtype.val ρ).push x.val)
          (lp_rel_m φ X.weaken (Fin.cases .newest (fun i => (e i).weaken))) := by
      have h := ih (ρ.push x) X.weaken (Fin.cases .newest (fun i => (e i).weaken))
        (by simpa only [Definitional.Term.eval_weaken] using closed)
      rw [image_env_push_l (M := rt_model_l Y ny) (N := M) Subtype.val ρ x] at h
      exact h
    simp only [lp_rel_m, Formula.satisfies_exists_iff, Formula.satisfies_forall_iff,
      Formula.satisfies_conj_iff, Formula.satisfies_imp_iff, Formula.satisfies_subset_iff,
      Definitional.Term.eval_newest, Definitional.Term.eval_weaken,
      eval_image_env_l (M := rt_model_l Y ny) (N := M) Subtype.val]
    first
    | exact ⟨fun ⟨x, hx, hh⟩ => ⟨x.val, (sub x).mp hx, (step x).mp hh⟩,
        fun ⟨x, hx, hh⟩ => ⟨⟨x, closed x hx⟩, (sub _).mpr hx, (step _).mpr hh⟩⟩
    | exact ⟨fun h x hx => (step ⟨x, closed x hx⟩).mp (h ⟨x, closed x hx⟩ ((sub _).mpr hx)),
        fun h x hx => (step x).mpr (h x.val ((sub x).mp hx))⟩

end YesMetaZFC.SetTheory.Internal

/-! ## 任意较低秩层的原满足公式

只以 Vν 为参数，把原前驱满足程序的量词限制到 Vν 的子集。
V(ν+1) 在证明中实际构造，在公式中不作为见证；这保留紧邻秩层的边界。
-/
namespace YesMetaZFC.SetTheory.Internal
open Definitional.Project InnerModel
universe u
variable {M : Structure.{u}}

def ft_lower_m {d} (X ω F n r f : Term d) : Formula 1 d :=
  lp_rel_m (ft_prev_m (.bound 4) (.bound 3) (.bound 2) (.bound 1) (.newest : Term 5)) X
    (Fin.cases f (Fin.cases r (Fin.cases n (Fin.cases F (fun _ => ω)))))

@[simp] theorem ft_lower_closed_l {d} (X ω F n r f : Term d)
    (hX : X.freeSupport = []) (hω : ω.freeSupport = []) (hF : F.freeSupport = [])
    (hn : n.freeSupport = []) (hr : r.freeSupport = []) (hf : f.freeSupport = []) :
    (ft_lower_m X ω F n r f).FreeClosed :=
  lp_rel_closed_l _ (ft_prev_m_freeClosed _ _ _ _ _ rfl rfl rfl rfl rfl) X _ hX
    (Fin.cases hf (Fin.cases hr (Fin.cases hn (Fin.cases hF (fun _ => hω)))))

variable (hZF : M.Models ZF)
local notation "I" => kp_pair_l (ZF.modelsKP hZF)
local notation "K" => fp_interpretation_l (ZF.models_kpi_l hZF)

theorem ft_lower_rank_l {d} (ρ : Env M d) (X ω F n r f : Term d) {ν c R a : M.Domain}
    (hω : M.IsOmega (ω.eval ρ)) (hV : V_d I ν (X.eval ρ)) (hων : M.MemberSubset (ω.eval ρ) ν)
    (hm : Smem_d K c (X.eval ρ) R) (ha : Sformula_d K (ω.eval ρ) a (n.eval ρ) (F.eval ρ) (r.eval ρ))
    (hf : M.IsSetFunctionFromTo K (f.eval ρ) (ω.eval ρ) (X.eval ρ)) :
    Formula.satisfies ρ (ft_lower_m X ω F n r f) ↔ Satisfies_d K (ω.eval ρ) c a (f.eval ρ) := by
  obtain ⟨μ, hs⟩ := KP.exists_successor (ZF.modelsKP hZF) ν
  obtain ⟨Y, hW⟩ := ZF.v_exists_l I hZF (KP.successor_isOrdinal (ZF.modelsKP hZF) (v_ordinal_l I hV) hs)
  have power := ZF.v_successor_l I hZF hV hW hs
  have nat : M.MemberSubset (ω.eval ρ) (X.eval ρ) := fun i hi => ZF.v_ordinal_mem_l I hZF hV (hων i hi)
  have hw := (power (ω.eval ρ)).mpr nat
  have hF := (power (F.eval ρ)).mpr (fp_program_rank_l I hZF hω hV hων ha.2.1)
  have hg := (power (f.eval ρ)).mpr (fp_function_rank_l I hZF hω hV hων nat hf)
  have ht := v_transitive_l I hW
  have hn := ht (ω.eval ρ) hw (n.eval ρ) ha.2.1.1
  have hr := ht (n.eval ρ) hn (r.eval ρ) ha.2.2
  let ny : Nonempty {x // M.mem x Y} := ⟨⟨ω.eval ρ, hw⟩⟩
  let N := rt_model_l Y ny
  let J := fp_rank_interpretation_l I hZF hω hW hw
  let G : N.Domain := ⟨F.eval ρ, hF⟩
  let l : N.Domain := ⟨n.eval ρ, hn⟩
  let k : N.Domain := ⟨r.eval ρ, hr⟩
  let g : N.Domain := ⟨f.eval ρ, hg⟩
  let η : Env N 5 := ⟨Fin.cases g (Fin.cases k (Fin.cases l (Fin.cases G (fun _ => ⟨ω.eval ρ, hw⟩)))), fun _ => g⟩
  exact (lp_rel_model_l ht ny _ (ft_prev_m_freeClosed _ _ _ _ _ rfl rfl rfl rfl rfl) η ρ X _ power
    (Fin.cases rfl (Fin.cases rfl (Fin.cases rfl (Fin.cases rfl (fun _ => rfl)))))).trans
      ((ft_prev_sat_l J (rt_model_ext_l hZF.1 ht ny) η (.bound 4) (.bound 3) (.bound 2) (.bound 1) .newest).trans
        (ft_prev_source_l I hZF hω hV hW hs hων hw G l k g hm ha hf))

/-- 外层仅需是一个包含 Vν 的秩层；其高度既可极限，也可恰为 ν+1。 -/
theorem ft_lower_source_l {Y η : M.Domain} (hY : V_d I η Y) (ny : Nonempty {x // M.mem x Y})
    {d} (ρ : Env (rt_model_l Y ny) d) (X ω F n r f : Term d) {ν c R a : M.Domain}
    (hω : M.IsOmega (ω.eval ρ).val) (hV : V_d I ν (X.eval ρ).val) (hων : M.MemberSubset (ω.eval ρ).val ν)
    (hm : Smem_d K c (X.eval ρ).val R)
    (ha : Sformula_d K (ω.eval ρ).val a (n.eval ρ).val (F.eval ρ).val (r.eval ρ).val)
    (hf : M.IsSetFunctionFromTo K (f.eval ρ).val (ω.eval ρ).val (X.eval ρ).val) :
    Formula.satisfies ρ (ft_lower_m X ω F n r f) ↔ Satisfies_d K (ω.eval ρ).val c a (f.eval ρ).val := by
  refine (lp_rel_absolute_l (v_transitive_l I hY) ny _ ρ X _
    (fun x hx => v_subset_mem_l I hY (X.eval ρ).property hx)).trans ?_
  have read := ft_lower_rank_l hZF (image_env_l (M := rt_model_l Y ny) (N := M) Subtype.val ρ)
    X ω F n r f (ν := ν) (c := c) (R := R) (a := a)
  simp only [eval_image_env_l (M := rt_model_l Y ny) (N := M) Subtype.val] at read
  exact read hω hV hων hm ha hf

end YesMetaZFC.SetTheory.Internal
