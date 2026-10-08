import CarrySelfAdjointOperator.CompletedNativeThetaEighthMomentCertificate
import CarrySelfAdjointOperator.CompletedNativeThetaSharpCurvature
namespace CarrySelfAdjointOperator
set_option maxHeartbeats 4000000
theorem thetaTwelfth_cell_curvature_064 :
    ∀ u ∈ Set.Icc (1/8:ℝ) (65/512:ℝ), (771616988138548525625321/500000000000000000000000:ℝ) ≤ thetaFirstModeSecond u := by
  have hlo : (126552254761/31250000000:ℝ) ≤ Real.pi*Real.exp (2*(65/512:ℝ)) := by
    calc
      _ ≤ (3141592/1000000:ℝ)*∑ i ∈ Finset.range 20, (2*(65/512:ℝ))^i/i.factorial := by
        norm_num [Finset.sum_range_succ]
      _ ≤ _ := mul_le_mul (by linarith [Real.pi_gt_d6])
        (Real.sum_le_exp_of_nonneg (by norm_num) 20)
        (Finset.sum_nonneg (fun i _ => by positivity)) Real.pi_pos.le
  have h := thetaFirstModeSecond_endpoint_cell_lower (1/8:ℝ) (65/512:ℝ) (126552254761/31250000000:ℝ) (3714040946007/100000000000000:ℝ)
    (by norm_num) (by norm_num) hlo (by norm_num) (thetaFirstMode_refined_node_0193).1
  intro u hu
  exact (show (771616988138548525625321/500000000000000000000000:ℝ) ≤ (1/4-6*(126552254761/31250000000:ℝ)+4*(126552254761/31250000000:ℝ)^2)*(3714040946007/100000000000000:ℝ) by norm_num).trans (h u hu)

theorem thetaTwelfth_cell_curvature_065 :
    ∀ u ∈ Set.Icc (65/512:ℝ) (33/256:ℝ), (1535797490155883452378041/1000000000000000000000000:ℝ) ≤ thetaFirstModeSecond u := by
  have hlo : (1016380530253/250000000000:ℝ) ≤ Real.pi*Real.exp (2*(33/256:ℝ)) := by
    calc
      _ ≤ (3141592/1000000:ℝ)*∑ i ∈ Finset.range 20, (2*(33/256:ℝ))^i/i.factorial := by
        norm_num [Finset.sum_range_succ]
      _ ≤ _ := mul_le_mul (by linarith [Real.pi_gt_d6])
        (Real.sum_le_exp_of_nonneg (by norm_num) 20)
        (Finset.sum_nonneg (fun i _ => by positivity)) Real.pi_pos.le
  have h := thetaFirstModeSecond_endpoint_cell_lower (65/512:ℝ) (33/256:ℝ) (1016380530253/250000000000:ℝ) (3659209265657/100000000000000:ℝ)
    (by norm_num) (by norm_num) hlo (by norm_num) (thetaFirstMode_refined_node_0198).1
  intro u hu
  exact (show (1535797490155883452378041/1000000000000000000000000:ℝ) ≤ (1/4-6*(1016380530253/250000000000:ℝ)+4*(1016380530253/250000000000:ℝ)^2)*(3659209265657/100000000000000:ℝ) by norm_num).trans (h u hu)

theorem thetaTwelfth_cell_curvature_066 :
    ∀ u ∈ Set.Icc (33/256:ℝ) (67/512:ℝ), (382070368022873068008451/250000000000000000000000:ℝ) ≤ thetaFirstModeSecond u := by
  have hlo : (4081434124697/1000000000000:ℝ) ≤ Real.pi*Real.exp (2*(67/512:ℝ)) := by
    calc
      _ ≤ (3141592/1000000:ℝ)*∑ i ∈ Finset.range 20, (2*(67/512:ℝ))^i/i.factorial := by
        norm_num [Finset.sum_range_succ]
      _ ≤ _ := mul_le_mul (by linarith [Real.pi_gt_d6])
        (Real.sum_le_exp_of_nonneg (by norm_num) 20)
        (Finset.sum_nonneg (fun i _ => by positivity)) Real.pi_pos.le
  have h := thetaFirstModeSecond_endpoint_cell_lower (33/256:ℝ) (67/512:ℝ) (4081434124697/1000000000000:ℝ) (360496344351/10000000000000:ℝ)
    (by norm_num) (by norm_num) hlo (by norm_num) (thetaFirstMode_refined_node_0199).1
  intro u hu
  exact (show (382070368022873068008451/250000000000000000000000:ℝ) ≤ (1/4-6*(4081434124697/1000000000000:ℝ)+4*(4081434124697/1000000000000:ℝ)^2)*(360496344351/10000000000000:ℝ) by norm_num).trans (h u hu)

theorem thetaTwelfth_cell_curvature_067 :
    ∀ u ∈ Set.Icc (67/512:ℝ) (17/128:ℝ), (1520687241082132602176131/1000000000000000000000000:ℝ) ≤ thetaFirstModeSecond u := by
  have hlo : (4097408406203/1000000000000:ℝ) ≤ Real.pi*Real.exp (2*(17/128:ℝ)) := by
    calc
      _ ≤ (3141592/1000000:ℝ)*∑ i ∈ Finset.range 20, (2*(17/128:ℝ))^i/i.factorial := by
        norm_num [Finset.sum_range_succ]
      _ ≤ _ := mul_le_mul (by linarith [Real.pi_gt_d6])
        (Real.sum_le_exp_of_nonneg (by norm_num) 20)
        (Finset.sum_nonneg (fun i _ => by positivity)) Real.pi_pos.le
  have h := thetaFirstModeSecond_endpoint_cell_lower (67/512:ℝ) (17/128:ℝ) (4097408406203/1000000000000:ℝ) (1775650306231/50000000000000:ℝ)
    (by norm_num) (by norm_num) hlo (by norm_num) (thetaFirstMode_refined_node_0204).1
  intro u hu
  exact (show (1520687241082132602176131/1000000000000000000000000:ℝ) ≤ (1/4-6*(4097408406203/1000000000000:ℝ)+4*(4097408406203/1000000000000:ℝ)^2)*(1775650306231/50000000000000:ℝ) by norm_num).trans (h u hu)

theorem thetaTwelfth_cell_curvature_068 :
    ∀ u ∈ Set.Icc (17/128:ℝ) (69/512:ℝ), (151301612701023632113533/100000000000000000000000:ℝ) ≤ thetaFirstModeSecond u := by
  have hlo : (2056722604639/500000000000:ℝ) ≤ Real.pi*Real.exp (2*(69/512:ℝ)) := by
    calc
      _ ≤ (3141592/1000000:ℝ)*∑ i ∈ Finset.range 20, (2*(69/512:ℝ))^i/i.factorial := by
        norm_num [Finset.sum_range_succ]
      _ ≤ _ := mul_le_mul (by linarith [Real.pi_gt_d6])
        (Real.sum_le_exp_of_nonneg (by norm_num) 20)
        (Finset.sum_nonneg (fun i _ => by positivity)) Real.pi_pos.le
  have h := thetaFirstModeSecond_endpoint_cell_lower (17/128:ℝ) (69/512:ℝ) (2056722604639/500000000000:ℝ) (3498217875589/100000000000000:ℝ)
    (by norm_num) (by norm_num) hlo (by norm_num) (thetaFirstMode_refined_node_0205).1
  intro u hu
  exact (show (151301612701023632113533/100000000000000000000000:ℝ) ≤ (1/4-6*(2056722604639/500000000000:ℝ)+4*(2056722604639/500000000000:ℝ)^2)*(3498217875589/100000000000000:ℝ) by norm_num).trans (h u hu)

theorem thetaTwelfth_cell_curvature_069 :
    ∀ u ∈ Set.Icc (69/512:ℝ) (35/256:ℝ), (1505269470331555588058513/1000000000000000000000000:ℝ) ≤ thetaFirstModeSecond u := by
  have hlo : (4129544778627/1000000000000:ℝ) ≤ Real.pi*Real.exp (2*(35/256:ℝ)) := by
    calc
      _ ≤ (3141592/1000000:ℝ)*∑ i ∈ Finset.range 20, (2*(35/256:ℝ))^i/i.factorial := by
        norm_num [Finset.sum_range_succ]
      _ ≤ _ := mul_le_mul (by linarith [Real.pi_gt_d6])
        (Real.sum_le_exp_of_nonneg (by norm_num) 20)
        (Finset.sum_nonneg (fun i _ => by positivity)) Real.pi_pos.le
  have h := thetaFirstModeSecond_endpoint_cell_lower (69/512:ℝ) (35/256:ℝ) (4129544778627/1000000000000:ℝ) (689142461327/20000000000000:ℝ)
    (by norm_num) (by norm_num) hlo (by norm_num) (thetaFirstMode_refined_node_0210).1
  intro u hu
  exact (show (1505269470331555588058513/1000000000000000000000000:ℝ) ≤ (1/4-6*(4129544778627/1000000000000:ℝ)+4*(4129544778627/1000000000000:ℝ)^2)*(689142461327/20000000000000:ℝ) by norm_num).trans (h u hu)

theorem thetaTwelfth_cell_curvature_070 :
    ∀ u ∈ Set.Icc (35/256:ℝ) (71/512:ℝ), (748724310880892193048397/500000000000000000000000:ℝ) ≤ thetaFirstModeSecond u := by
  have hlo : (1036426839977/250000000000:ℝ) ≤ Real.pi*Real.exp (2*(71/512:ℝ)) := by
    calc
      _ ≤ (3141592/1000000:ℝ)*∑ i ∈ Finset.range 20, (2*(71/512:ℝ))^i/i.factorial := by
        norm_num [Finset.sum_range_succ]
      _ ≤ _ := mul_le_mul (by linarith [Real.pi_gt_d6])
        (Real.sum_le_exp_of_nonneg (by norm_num) 20)
        (Finset.sum_nonneg (fun i _ => by positivity)) Real.pi_pos.le
  have h := thetaFirstModeSecond_endpoint_cell_lower (35/256:ℝ) (71/512:ℝ) (1036426839977/250000000000:ℝ) (3393780950527/100000000000000:ℝ)
    (by norm_num) (by norm_num) hlo (by norm_num) (thetaFirstMode_refined_node_0211).1
  intro u hu
  exact (show (748724310880892193048397/500000000000000000000000:ℝ) ≤ (1/4-6*(1036426839977/250000000000:ℝ)+4*(1036426839977/250000000000:ℝ)^2)*(3393780950527/100000000000000:ℝ) by norm_num).trans (h u hu)

theorem thetaTwelfth_cell_curvature_071 :
    ∀ u ∈ Set.Icc (71/512:ℝ) (9/64:ℝ), (744777470984011550919633/500000000000000000000000:ℝ) ≤ thetaFirstModeSecond u := by
  have hlo : (32515103123/7812500000:ℝ) ≤ Real.pi*Real.exp (2*(9/64:ℝ)) := by
    calc
      _ ≤ (3141592/1000000:ℝ)*∑ i ∈ Finset.range 20, (2*(9/64:ℝ))^i/i.factorial := by
        norm_num [Finset.sum_range_succ]
      _ ≤ _ := mul_le_mul (by linarith [Real.pi_gt_d6])
        (Real.sum_le_exp_of_nonneg (by norm_num) 20)
        (Finset.sum_nonneg (fun i _ => by positivity)) Real.pi_pos.le
  have h := thetaFirstModeSecond_endpoint_cell_lower (71/512:ℝ) (9/64:ℝ) (32515103123/7812500000:ℝ) (3342420823879/100000000000000:ℝ)
    (by norm_num) (by norm_num) hlo (by norm_num) (thetaFirstMode_refined_node_0216).1
  intro u hu
  exact (show (744777470984011550919633/500000000000000000000000:ℝ) ≤ (1/4-6*(32515103123/7812500000:ℝ)+4*(32515103123/7812500000:ℝ)^2)*(3342420823879/100000000000000:ℝ) by norm_num).trans (h u hu)

theorem thetaTwelfth_cell_curvature_072 :
    ∀ u ∈ Set.Icc (9/64:ℝ) (73/512:ℝ), (370397450314778713904079/250000000000000000000000:ℝ) ≤ thetaFirstModeSecond u := by
  have hlo : (4178222545721/1000000000000:ℝ) ≤ Real.pi*Real.exp (2*(73/512:ℝ)) := by
    calc
      _ ≤ (3141592/1000000:ℝ)*∑ i ∈ Finset.range 20, (2*(73/512:ℝ))^i/i.factorial := by
        norm_num [Finset.sum_range_succ]
      _ ≤ _ := mul_le_mul (by linarith [Real.pi_gt_d6])
        (Real.sum_le_exp_of_nonneg (by norm_num) 20)
        (Finset.sum_nonneg (fun i _ => by positivity)) Real.pi_pos.le
  have h := thetaFirstModeSecond_endpoint_cell_lower (9/64:ℝ) (73/512:ℝ) (4178222545721/1000000000000:ℝ) (658325783107/20000000000000:ℝ)
    (by norm_num) (by norm_num) hlo (by norm_num) (thetaFirstMode_refined_node_0217).1
  intro u hu
  exact (show (370397450314778713904079/250000000000000000000000:ℝ) ≤ (1/4-6*(4178222545721/1000000000000:ℝ)+4*(4178222545721/1000000000000:ℝ)^2)*(658325783107/20000000000000:ℝ) by norm_num).trans (h u hu)

theorem thetaTwelfth_cell_curvature_073 :
    ∀ u ∈ Set.Icc (73/512:ℝ) (37/256:ℝ), (368388644815982758205847/250000000000000000000000:ℝ) ≤ thetaFirstModeSecond u := by
  have hlo : (1048643911599/250000000000:ℝ) ≤ Real.pi*Real.exp (2*(37/256:ℝ)) := by
    calc
      _ ≤ (3141592/1000000:ℝ)*∑ i ∈ Finset.range 20, (2*(37/256:ℝ))^i/i.factorial := by
        norm_num [Finset.sum_range_succ]
      _ ≤ _ := mul_le_mul (by linarith [Real.pi_gt_d6])
        (Real.sum_le_exp_of_nonneg (by norm_num) 20)
        (Finset.sum_nonneg (fun i _ => by positivity)) Real.pi_pos.le
  have h := thetaFirstModeSecond_endpoint_cell_lower (73/512:ℝ) (37/256:ℝ) (1048643911599/250000000000:ℝ) (129656087483/4000000000000:ℝ)
    (by norm_num) (by norm_num) hlo (by norm_num) (thetaFirstMode_refined_node_0222).1
  intro u hu
  exact (show (368388644815982758205847/250000000000000000000000:ℝ) ≤ (1/4-6*(1048643911599/250000000000:ℝ)+4*(1048643911599/250000000000:ℝ)^2)*(129656087483/4000000000000:ℝ) by norm_num).trans (h u hu)

theorem thetaTwelfth_cell_curvature_074 :
    ∀ u ∈ Set.Icc (37/256:ℝ) (75/512:ℝ), (1465450664616607846771403/1000000000000000000000000:ℝ) ≤ thetaFirstModeSecond u := by
  have hlo : (2105496375649/500000000000:ℝ) ≤ Real.pi*Real.exp (2*(75/512:ℝ)) := by
    calc
      _ ≤ (3141592/1000000:ℝ)*∑ i ∈ Finset.range 20, (2*(75/512:ℝ))^i/i.factorial := by
        norm_num [Finset.sum_range_succ]
      _ ≤ _ := mul_le_mul (by linarith [Real.pi_gt_d6])
        (Real.sum_le_exp_of_nonneg (by norm_num) 20)
        (Finset.sum_nonneg (fun i _ => by positivity)) Real.pi_pos.le
  have h := thetaFirstModeSecond_endpoint_cell_lower (37/256:ℝ) (75/512:ℝ) (2105496375649/500000000000:ℝ) (1595868786681/50000000000000:ℝ)
    (by norm_num) (by norm_num) hlo (by norm_num) (thetaFirstMode_refined_node_0223).1
  intro u hu
  exact (show (1465450664616607846771403/1000000000000000000000000:ℝ) ≤ (1/4-6*(2105496375649/500000000000:ℝ)+4*(2105496375649/500000000000:ℝ)^2)*(1595868786681/50000000000000:ℝ) by norm_num).trans (h u hu)

theorem thetaTwelfth_cell_curvature_075 :
    ∀ u ∈ Set.Icc (75/512:ℝ) (19/128:ℝ), (1457279454603692893258001/1000000000000000000000000:ℝ) ≤ thetaFirstModeSecond u := by
  have hlo : (4227474110931/1000000000000:ℝ) ≤ Real.pi*Real.exp (2*(19/128:ℝ)) := by
    calc
      _ ≤ (3141592/1000000:ℝ)*∑ i ∈ Finset.range 20, (2*(19/128:ℝ))^i/i.factorial := by
        norm_num [Finset.sum_range_succ]
      _ ≤ _ := mul_le_mul (by linarith [Real.pi_gt_d6])
        (Real.sum_le_exp_of_nonneg (by norm_num) 20)
        (Finset.sum_nonneg (fun i _ => by positivity)) Real.pi_pos.le
  have h := thetaFirstModeSecond_endpoint_cell_lower (75/512:ℝ) (19/128:ℝ) (4227474110931/1000000000000:ℝ) (785657995753/25000000000000:ℝ)
    (by norm_num) (by norm_num) hlo (by norm_num) (thetaFirstMode_refined_node_0228).1
  intro u hu
  exact (show (1457279454603692893258001/1000000000000000000000000:ℝ) ≤ (1/4-6*(4227474110931/1000000000000:ℝ)+4*(4227474110931/1000000000000:ℝ)^2)*(785657995753/25000000000000:ℝ) by norm_num).trans (h u hu)

theorem thetaTwelfth_cell_curvature_076 :
    ∀ u ∈ Set.Icc (19/128:ℝ) (77/512:ℝ), (1449042354883298170445393/1000000000000000000000000:ℝ) ≤ thetaFirstModeSecond u := by
  have hlo : (2122009988391/500000000000:ℝ) ≤ Real.pi*Real.exp (2*(77/512:ℝ)) := by
    calc
      _ ≤ (3141592/1000000:ℝ)*∑ i ∈ Finset.range 20, (2*(77/512:ℝ))^i/i.factorial := by
        norm_num [Finset.sum_range_succ]
      _ ≤ _ := mul_le_mul (by linarith [Real.pi_gt_d6])
        (Real.sum_le_exp_of_nonneg (by norm_num) 20)
        (Finset.sum_nonneg (fun i _ => by positivity)) Real.pi_pos.le
  have h := thetaFirstModeSecond_endpoint_cell_lower (19/128:ℝ) (77/512:ℝ) (2122009988391/500000000000:ℝ) (1547041149511/50000000000000:ℝ)
    (by norm_num) (by norm_num) hlo (by norm_num) (thetaFirstMode_refined_node_0229).1
  intro u hu
  exact (show (1449042354883298170445393/1000000000000000000000000:ℝ) ≤ (1/4-6*(2122009988391/500000000000:ℝ)+4*(2122009988391/500000000000:ℝ)^2)*(1547041149511/50000000000000:ℝ) by norm_num).trans (h u hu)

theorem thetaTwelfth_cell_curvature_077 :
    ∀ u ∈ Set.Icc (77/512:ℝ) (39/256:ℝ), (57629631164214578349543/40000000000000000000000:ℝ) ≤ thetaFirstModeSecond u := by
  have hlo : (4260630601321/1000000000000:ℝ) ≤ Real.pi*Real.exp (2*(39/256:ℝ)) := by
    calc
      _ ≤ (3141592/1000000:ℝ)*∑ i ∈ Finset.range 20, (2*(39/256:ℝ))^i/i.factorial := by
        norm_num [Finset.sum_range_succ]
      _ ≤ _ := mul_le_mul (by linarith [Real.pi_gt_d6])
        (Real.sum_le_exp_of_nonneg (by norm_num) 20)
        (Finset.sum_nonneg (fun i _ => by positivity)) Real.pi_pos.le
  have h := thetaFirstModeSecond_endpoint_cell_lower (77/512:ℝ) (39/256:ℝ) (4260630601321/1000000000000:ℝ) (380760672401/12500000000000:ℝ)
    (by norm_num) (by norm_num) hlo (by norm_num) (thetaFirstMode_refined_node_0234).1
  intro u hu
  exact (show (57629631164214578349543/40000000000000000000000:ℝ) ≤ (1/4-6*(4260630601321/1000000000000:ℝ)+4*(4260630601321/1000000000000:ℝ)^2)*(380760672401/12500000000000:ℝ) by norm_num).trans (h u hu)

theorem thetaTwelfth_cell_curvature_078 :
    ∀ u ∈ Set.Icc (39/256:ℝ) (79/512:ℝ), (358094037155113844769399/250000000000000000000000:ℝ) ≤ thetaFirstModeSecond u := by
  have hlo : (2138653119003/500000000000:ℝ) ≤ Real.pi*Real.exp (2*(79/512:ℝ)) := by
    calc
      _ ≤ (3141592/1000000:ℝ)*∑ i ∈ Finset.range 20, (2*(79/512:ℝ))^i/i.factorial := by
        norm_num [Finset.sum_range_succ]
      _ ≤ _ := mul_le_mul (by linarith [Real.pi_gt_d6])
        (Real.sum_le_exp_of_nonneg (by norm_num) 20)
        (Finset.sum_nonneg (fun i _ => by positivity)) Real.pi_pos.le
  have h := thetaFirstModeSecond_endpoint_cell_lower (39/256:ℝ) (79/512:ℝ) (2138653119003/500000000000:ℝ) (1499319028417/50000000000000:ℝ)
    (by norm_num) (by norm_num) hlo (by norm_num) (thetaFirstMode_refined_node_0235).1
  intro u hu
  exact (show (358094037155113844769399/250000000000000000000000:ℝ) ≤ (1/4-6*(2138653119003/500000000000:ℝ)+4*(2138653119003/500000000000:ℝ)^2)*(1499319028417/50000000000000:ℝ) by norm_num).trans (h u hu)

theorem thetaTwelfth_cell_curvature_079 :
    ∀ u ∈ Set.Icc (79/512:ℝ) (5/32:ℝ), (142394989210521566569459/100000000000000000000000:ℝ) ≤ thetaFirstModeSecond u := by
  have hlo : (536755892661/125000000000:ℝ) ≤ Real.pi*Real.exp (2*(5/32:ℝ)) := by
    calc
      _ ≤ (3141592/1000000:ℝ)*∑ i ∈ Finset.range 20, (2*(5/32:ℝ))^i/i.factorial := by
        norm_num [Finset.sum_range_succ]
      _ ≤ _ := mul_le_mul (by linarith [Real.pi_gt_d6])
        (Real.sum_le_exp_of_nonneg (by norm_num) 20)
        (Finset.sum_nonneg (fun i _ => by positivity)) Real.pi_pos.le
  have h := thetaFirstModeSecond_endpoint_cell_lower (79/512:ℝ) (5/32:ℝ) (536755892661/125000000000:ℝ) (184483571317/6250000000000:ℝ)
    (by norm_num) (by norm_num) hlo (by norm_num) (thetaFirstMode_refined_node_0240).1
  intro u hu
  exact (show (142394989210521566569459/100000000000000000000000:ℝ) ≤ (1/4-6*(536755892661/125000000000:ℝ)+4*(536755892661/125000000000:ℝ)^2)*(184483571317/6250000000000:ℝ) by norm_num).trans (h u hu)

theorem thetaTwelfth_cell_curvature_080 :
    ∀ u ∈ Set.Icc (5/32:ℝ) (81/512:ℝ), (707731722623356296678787/500000000000000000000000:ℝ) ≤ thetaFirstModeSecond u := by
  have hlo : (1077713391653/250000000000:ℝ) ≤ Real.pi*Real.exp (2*(81/512:ℝ)) := by
    calc
      _ ≤ (3141592/1000000:ℝ)*∑ i ∈ Finset.range 20, (2*(81/512:ℝ))^i/i.factorial := by
        norm_num [Finset.sum_range_succ]
      _ ≤ _ := mul_le_mul (by linarith [Real.pi_gt_d6])
        (Real.sum_le_exp_of_nonneg (by norm_num) 20)
        (Finset.sum_nonneg (fun i _ => by positivity)) Real.pi_pos.le
  have h := thetaFirstModeSecond_endpoint_cell_lower (5/32:ℝ) (81/512:ℝ) (1077713391653/250000000000:ℝ) (2905379417603/100000000000000:ℝ)
    (by norm_num) (by norm_num) hlo (by norm_num) (thetaFirstMode_refined_node_0241).1
  intro u hu
  exact (show (707731722623356296678787/500000000000000000000000:ℝ) ≤ (1/4-6*(1077713391653/250000000000:ℝ)+4*(1077713391653/250000000000:ℝ)^2)*(2905379417603/100000000000000:ℝ) by norm_num).trans (h u hu)

theorem thetaTwelfth_cell_curvature_081 :
    ∀ u ∈ Set.Icc (81/512:ℝ) (41/256:ℝ), (140691825040653213041507/100000000000000000000000:ℝ) ≤ thetaFirstModeSecond u := by
  have hlo : (2163862885213/500000000000:ℝ) ≤ Real.pi*Real.exp (2*(41/256:ℝ)) := by
    calc
      _ ≤ (3141592/1000000:ℝ)*∑ i ∈ Finset.range 20, (2*(41/256:ℝ))^i/i.factorial := by
        norm_num [Finset.sum_range_succ]
      _ ≤ _ := mul_le_mul (by linarith [Real.pi_gt_d6])
        (Real.sum_le_exp_of_nonneg (by norm_num) 20)
        (Finset.sum_nonneg (fun i _ => by positivity)) Real.pi_pos.le
  have h := thetaFirstModeSecond_endpoint_cell_lower (81/512:ℝ) (41/256:ℝ) (2163862885213/500000000000:ℝ) (178722603073/6250000000000:ℝ)
    (by norm_num) (by norm_num) hlo (by norm_num) (thetaFirstMode_refined_node_0246).1
  intro u hu
  exact (show (140691825040653213041507/100000000000000000000000:ℝ) ≤ (1/4-6*(2163862885213/500000000000:ℝ)+4*(2163862885213/500000000000:ℝ)^2)*(178722603073/6250000000000:ℝ) by norm_num).trans (h u hu)

theorem thetaTwelfth_cell_curvature_082 :
    ∀ u ∈ Set.Icc (41/256:ℝ) (83/512:ℝ), (1398315756235929239638543/1000000000000000000000000:ℝ) ≤ thetaFirstModeSecond u := by
  have hlo : (2172332005089/500000000000:ℝ) ≤ Real.pi*Real.exp (2*(83/512:ℝ)) := by
    calc
      _ ≤ (3141592/1000000:ℝ)*∑ i ∈ Finset.range 20, (2*(83/512:ℝ))^i/i.factorial := by
        norm_num [Finset.sum_range_succ]
      _ ≤ _ := mul_le_mul (by linarith [Real.pi_gt_d6])
        (Real.sum_le_exp_of_nonneg (by norm_num) 20)
        (Finset.sum_nonneg (fun i _ => by positivity)) Real.pi_pos.le
  have h := thetaFirstModeSecond_endpoint_cell_lower (41/256:ℝ) (83/512:ℝ) (2172332005089/500000000000:ℝ) (175892536003/6250000000000:ℝ)
    (by norm_num) (by norm_num) hlo (by norm_num) (thetaFirstMode_refined_node_0247).1
  intro u hu
  exact (show (1398315756235929239638543/1000000000000000000000000:ℝ) ≤ (1/4-6*(2172332005089/500000000000:ℝ)+4*(2172332005089/500000000000:ℝ)^2)*(175892536003/6250000000000:ℝ) by norm_num).trans (h u hu)

theorem thetaTwelfth_cell_curvature_083 :
    ∀ u ∈ Set.Icc (83/512:ℝ) (21/128:ℝ), (69482870869170007236767/50000000000000000000000:ℝ) ≤ thetaFirstModeSecond u := by
  have hlo : (2180834272163/500000000000:ℝ) ≤ Real.pi*Real.exp (2*(21/128:ℝ)) := by
    calc
      _ ≤ (3141592/1000000:ℝ)*∑ i ∈ Finset.range 20, (2*(21/128:ℝ))^i/i.factorial := by
        norm_num [Finset.sum_range_succ]
      _ ≤ _ := mul_le_mul (by linarith [Real.pi_gt_d6])
        (Real.sum_le_exp_of_nonneg (by norm_num) 20)
        (Finset.sum_nonneg (fun i _ => by positivity)) Real.pi_pos.le
  have h := thetaFirstModeSecond_endpoint_cell_lower (83/512:ℝ) (21/128:ℝ) (2180834272163/500000000000:ℝ) (1384766458359/50000000000000:ℝ)
    (by norm_num) (by norm_num) hlo (by norm_num) (thetaFirstMode_refined_node_0252).1
  intro u hu
  exact (show (69482870869170007236767/50000000000000000000000:ℝ) ≤ (1/4-6*(2180834272163/500000000000:ℝ)+4*(2180834272163/500000000000:ℝ)^2)*(1384766458359/50000000000000:ℝ) by norm_num).trans (h u hu)

theorem thetaTwelfth_cell_curvature_084 :
    ∀ u ∈ Set.Icc (21/128:ℝ) (85/512:ℝ), (55237787764003379295427/40000000000000000000000:ℝ) ≤ thetaFirstModeSecond u := by
  have hlo : (4378739632339/1000000000000:ℝ) ≤ Real.pi*Real.exp (2*(85/512:ℝ)) := by
    calc
      _ ≤ (3141592/1000000:ℝ)*∑ i ∈ Finset.range 20, (2*(85/512:ℝ))^i/i.factorial := by
        norm_num [Finset.sum_range_succ]
      _ ≤ _ := mul_le_mul (by linarith [Real.pi_gt_d6])
        (Real.sum_le_exp_of_nonneg (by norm_num) 20)
        (Finset.sum_nonneg (fun i _ => by positivity)) Real.pi_pos.le
  have h := thetaFirstModeSecond_endpoint_cell_lower (21/128:ℝ) (85/512:ℝ) (4378739632339/1000000000000:ℝ) (545063073663/20000000000000:ℝ)
    (by norm_num) (by norm_num) hlo (by norm_num) (thetaFirstMode_refined_node_0253).1
  intro u hu
  exact (show (55237787764003379295427/40000000000000000000000:ℝ) ≤ (1/4-6*(4378739632339/1000000000000:ℝ)+4*(4378739632339/1000000000000:ℝ)^2)*(545063073663/20000000000000:ℝ) by norm_num).trans (h u hu)

theorem thetaTwelfth_cell_curvature_085 :
    ∀ u ∈ Set.Icc (85/512:ℝ) (43/256:ℝ), (27443581038305592302033/20000000000000000000000:ℝ) ≤ thetaFirstModeSecond u := by
  have hlo : (2197938767351/500000000000:ℝ) ≤ Real.pi*Real.exp (2*(43/256:ℝ)) := by
    calc
      _ ≤ (3141592/1000000:ℝ)*∑ i ∈ Finset.range 20, (2*(43/256:ℝ))^i/i.factorial := by
        norm_num [Finset.sum_range_succ]
      _ ≤ _ := mul_le_mul (by linarith [Real.pi_gt_d6])
        (Real.sum_le_exp_of_nonneg (by norm_num) 20)
        (Finset.sum_nonneg (fun i _ => by positivity)) Real.pi_pos.le
  have h := thetaFirstModeSecond_endpoint_cell_lower (85/512:ℝ) (43/256:ℝ) (2197938767351/500000000000:ℝ) (167601537953/6250000000000:ℝ)
    (by norm_num) (by norm_num) hlo (by norm_num) (thetaFirstMode_refined_node_0258).1
  intro u hu
  exact (show (27443581038305592302033/20000000000000000000000:ℝ) ≤ (1/4-6*(2197938767351/500000000000:ℝ)+4*(2197938767351/500000000000:ℝ)^2)*(167601537953/6250000000000:ℝ) by norm_num).trans (h u hu)

theorem thetaTwelfth_cell_curvature_086 :
    ∀ u ∈ Set.Icc (43/256:ℝ) (87/512:ℝ), (1363361961265949616345863/1000000000000000000000000:ℝ) ≤ thetaFirstModeSecond u := by
  have hlo : (4413082512917/1000000000000:ℝ) ≤ Real.pi*Real.exp (2*(87/512:ℝ)) := by
    calc
      _ ≤ (3141592/1000000:ℝ)*∑ i ∈ Finset.range 20, (2*(87/512:ℝ))^i/i.factorial := by
        norm_num [Finset.sum_range_succ]
      _ ≤ _ := mul_le_mul (by linarith [Real.pi_gt_d6])
        (Real.sum_le_exp_of_nonneg (by norm_num) 20)
        (Finset.sum_nonneg (fun i _ => by positivity)) Real.pi_pos.le
  have h := thetaFirstModeSecond_endpoint_cell_lower (43/256:ℝ) (87/512:ℝ) (4413082512917/1000000000000:ℝ) (2576618447/97656250000:ℝ)
    (by norm_num) (by norm_num) hlo (by norm_num) (thetaFirstMode_refined_node_0259).1
  intro u hu
  exact (show (1363361961265949616345863/1000000000000000000000000:ℝ) ≤ (1/4-6*(4413082512917/1000000000000:ℝ)+4*(4413082512917/1000000000000:ℝ)^2)*(2576618447/97656250000:ℝ) by norm_num).trans (h u hu)

theorem thetaTwelfth_cell_curvature_087 :
    ∀ u ∈ Set.Icc (87/512:ℝ) (11/64:ℝ), (677247448577648422409407/500000000000000000000000:ℝ) ≤ thetaFirstModeSecond u := by
  have hlo : (2215177414757/500000000000:ℝ) ≤ Real.pi*Real.exp (2*(11/64:ℝ)) := by
    calc
      _ ≤ (3141592/1000000:ℝ)*∑ i ∈ Finset.range 20, (2*(11/64:ℝ))^i/i.factorial := by
        norm_num [Finset.sum_range_succ]
      _ ≤ _ := mul_le_mul (by linarith [Real.pi_gt_d6])
        (Real.sum_le_exp_of_nonneg (by norm_num) 20)
        (Finset.sum_nonneg (fun i _ => by positivity)) Real.pi_pos.le
  have h := thetaFirstModeSecond_endpoint_cell_lower (87/512:ℝ) (11/64:ℝ) (2215177414757/500000000000:ℝ) (1297905026173/50000000000000:ℝ)
    (by norm_num) (by norm_num) hlo (by norm_num) (thetaFirstMode_refined_node_0264).1
  intro u hu
  exact (show (677247448577648422409407/500000000000000000000000:ℝ) ≤ (1/4-6*(2215177414757/500000000000:ℝ)+4*(2215177414757/500000000000:ℝ)^2)*(1297905026173/50000000000000:ℝ) by norm_num).trans (h u hu)

theorem thetaTwelfth_cell_curvature_088 :
    ∀ u ∈ Set.Icc (11/64:ℝ) (89/512:ℝ), (1345579338786648282695207/1000000000000000000000000:ℝ) ≤ thetaFirstModeSecond u := by
  have hlo : (2223847374023/500000000000:ℝ) ≤ Real.pi*Real.exp (2*(89/512:ℝ)) := by
    calc
      _ ≤ (3141592/1000000:ℝ)*∑ i ∈ Finset.range 20, (2*(89/512:ℝ))^i/i.factorial := by
        norm_num [Finset.sum_range_succ]
      _ ≤ _ := mul_le_mul (by linarith [Real.pi_gt_d6])
        (Real.sum_le_exp_of_nonneg (by norm_num) 20)
        (Finset.sum_nonneg (fun i _ => by positivity)) Real.pi_pos.le
  have h := thetaFirstModeSecond_endpoint_cell_lower (11/64:ℝ) (89/512:ℝ) (2223847374023/500000000000:ℝ) (319209939079/12500000000000:ℝ)
    (by norm_num) (by norm_num) hlo (by norm_num) (thetaFirstMode_refined_node_0265).1
  intro u hu
  exact (show (1345579338786648282695207/1000000000000000000000000:ℝ) ≤ (1/4-6*(2223847374023/500000000000:ℝ)+4*(2223847374023/500000000000:ℝ)^2)*(319209939079/12500000000000:ℝ) by norm_num).trans (h u hu)

theorem thetaTwelfth_cell_curvature_089 :
    ∀ u ∈ Set.Icc (89/512:ℝ) (45/256:ℝ), (41769274037795552817787/31250000000000000000000:ℝ) ≤ thetaFirstModeSecond u := by
  have hlo : (4465102533101/1000000000000:ℝ) ≤ Real.pi*Real.exp (2*(45/256:ℝ)) := by
    calc
      _ ≤ (3141592/1000000:ℝ)*∑ i ∈ Finset.range 20, (2*(45/256:ℝ))^i/i.factorial := by
        norm_num [Finset.sum_range_succ]
      _ ≤ _ := mul_le_mul (by linarith [Real.pi_gt_d6])
        (Real.sum_le_exp_of_nonneg (by norm_num) 20)
        (Finset.sum_nonneg (fun i _ => by positivity)) Real.pi_pos.le
  have h := thetaFirstModeSecond_endpoint_cell_lower (89/512:ℝ) (45/256:ℝ) (4465102533101/1000000000000:ℝ) (2512062269617/100000000000000:ℝ)
    (by norm_num) (by norm_num) hlo (by norm_num) (thetaFirstMode_refined_node_0270).1
  intro u hu
  exact (show (41769274037795552817787/31250000000000000000000:ℝ) ≤ (1/4-6*(4465102533101/1000000000000:ℝ)+4*(4465102533101/1000000000000:ℝ)^2)*(2512062269617/100000000000000:ℝ) by norm_num).trans (h u hu)

theorem thetaTwelfth_cell_curvature_090 :
    ∀ u ∈ Set.Icc (45/256:ℝ) (91/512:ℝ), (663804337474992033484227/500000000000000000000000:ℝ) ≤ thetaFirstModeSecond u := by
  have hlo : (44825784503/10000000000:ℝ) ≤ Real.pi*Real.exp (2*(91/512:ℝ)) := by
    calc
      _ ≤ (3141592/1000000:ℝ)*∑ i ∈ Finset.range 20, (2*(91/512:ℝ))^i/i.factorial := by
        norm_num [Finset.sum_range_succ]
      _ ≤ _ := mul_le_mul (by linarith [Real.pi_gt_d6])
        (Real.sum_le_exp_of_nonneg (by norm_num) 20)
        (Finset.sum_nonneg (fun i _ => by positivity)) Real.pi_pos.le
  have h := thetaFirstModeSecond_endpoint_cell_lower (45/256:ℝ) (91/512:ℝ) (44825784503/10000000000:ℝ) (2470954904391/100000000000000:ℝ)
    (by norm_num) (by norm_num) hlo (by norm_num) (thetaFirstMode_refined_node_0271).1
  intro u hu
  exact (show (663804337474992033484227/500000000000000000000000:ℝ) ≤ (1/4-6*(44825784503/10000000000:ℝ)+4*(44825784503/10000000000:ℝ)^2)*(2470954904391/100000000000000:ℝ) by norm_num).trans (h u hu)

theorem thetaTwelfth_cell_curvature_091 :
    ∀ u ∈ Set.Icc (91/512:ℝ) (23/128:ℝ), (659278272829284846706663/500000000000000000000000:ℝ) ≤ thetaFirstModeSecond u := by
  have hlo : (900024553261/200000000000:ℝ) ≤ Real.pi*Real.exp (2*(23/128:ℝ)) := by
    calc
      _ ≤ (3141592/1000000:ℝ)*∑ i ∈ Finset.range 20, (2*(23/128:ℝ))^i/i.factorial := by
        norm_num [Finset.sum_range_succ]
      _ ≤ _ := mul_le_mul (by linarith [Real.pi_gt_d6])
        (Real.sum_le_exp_of_nonneg (by norm_num) 20)
        (Finset.sum_nonneg (fun i _ => by positivity)) Real.pi_pos.le
  have h := thetaFirstModeSecond_endpoint_cell_lower (91/512:ℝ) (23/128:ℝ) (900024553261/200000000000:ℝ) (1215176990341/50000000000000:ℝ)
    (by norm_num) (by norm_num) hlo (by norm_num) (thetaFirstMode_refined_node_0276).1
  intro u hu
  exact (show (659278272829284846706663/500000000000000000000000:ℝ) ≤ (1/4-6*(900024553261/200000000000:ℝ)+4*(900024553261/200000000000:ℝ)^2)*(1215176990341/50000000000000:ℝ) by norm_num).trans (h u hu)

theorem thetaTwelfth_cell_curvature_092 :
    ∀ u ∈ Set.Icc (23/128:ℝ) (93/512:ℝ), (654730936874303803865293/500000000000000000000000:ℝ) ≤ thetaFirstModeSecond u := by
  have hlo : (4517735748821/1000000000000:ℝ) ≤ Real.pi*Real.exp (2*(93/512:ℝ)) := by
    calc
      _ ≤ (3141592/1000000:ℝ)*∑ i ∈ Finset.range 20, (2*(93/512:ℝ))^i/i.factorial := by
        norm_num [Finset.sum_range_succ]
      _ ≤ _ := mul_le_mul (by linarith [Real.pi_gt_d6])
        (Real.sum_le_exp_of_nonneg (by norm_num) 20)
        (Finset.sum_nonneg (fun i _ => by positivity)) Real.pi_pos.le
  have h := thetaFirstModeSecond_endpoint_cell_lower (23/128:ℝ) (93/512:ℝ) (4517735748821/1000000000000:ℝ) (2390256045431/100000000000000:ℝ)
    (by norm_num) (by norm_num) hlo (by norm_num) (thetaFirstMode_refined_node_0277).1
  intro u hu
  exact (show (654730936874303803865293/500000000000000000000000:ℝ) ≤ (1/4-6*(4517735748821/1000000000000:ℝ)+4*(4517735748821/1000000000000:ℝ)^2)*(2390256045431/100000000000000:ℝ) by norm_num).trans (h u hu)

theorem thetaTwelfth_cell_curvature_093 :
    ∀ u ∈ Set.Icc (93/512:ℝ) (47/256:ℝ), (260065230803511589920163/200000000000000000000000:ℝ) ≤ thetaFirstModeSecond u := by
  have hlo : (2267708833301/500000000000:ℝ) ≤ Real.pi*Real.exp (2*(47/256:ℝ)) := by
    calc
      _ ≤ (3141592/1000000:ℝ)*∑ i ∈ Finset.range 20, (2*(47/256:ℝ))^i/i.factorial := by
        norm_num [Finset.sum_range_succ]
      _ ≤ _ := mul_le_mul (by linarith [Real.pi_gt_d6])
        (Real.sum_le_exp_of_nonneg (by norm_num) 20)
        (Finset.sum_nonneg (fun i _ => by positivity)) Real.pi_pos.le
  have h := thetaFirstModeSecond_endpoint_cell_lower (93/512:ℝ) (47/256:ℝ) (2267708833301/500000000000:ℝ) (587664407333/25000000000000:ℝ)
    (by norm_num) (by norm_num) hlo (by norm_num) (thetaFirstMode_refined_node_0282).1
  intro u hu
  exact (show (260065230803511589920163/200000000000000000000000:ℝ) ≤ (1/4-6*(2267708833301/500000000000:ℝ)+4*(2267708833301/500000000000:ℝ)^2)*(587664407333/25000000000000:ℝ) by norm_num).trans (h u hu)

theorem thetaTwelfth_cell_curvature_094 :
    ∀ u ∈ Set.Icc (47/256:ℝ) (95/512:ℝ), (12911508832914503896323/10000000000000000000000:ℝ) ≤ thetaFirstModeSecond u := by
  have hlo : (1138292197363/250000000000:ℝ) ≤ Real.pi*Real.exp (2*(95/512:ℝ)) := by
    calc
      _ ≤ (3141592/1000000:ℝ)*∑ i ∈ Finset.range 20, (2*(95/512:ℝ))^i/i.factorial := by
        norm_num [Finset.sum_range_succ]
      _ ≤ _ := mul_le_mul (by linarith [Real.pi_gt_d6])
        (Real.sum_le_exp_of_nonneg (by norm_num) 20)
        (Finset.sum_nonneg (fun i _ => by positivity)) Real.pi_pos.le
  have h := thetaFirstModeSecond_endpoint_cell_lower (47/256:ℝ) (95/512:ℝ) (1138292197363/250000000000:ℝ) (92462209897/4000000000000:ℝ)
    (by norm_num) (by norm_num) hlo (by norm_num) (thetaFirstMode_refined_node_0283).1
  intro u hu
  exact (show (12911508832914503896323/10000000000000000000000:ℝ) ≤ (1/4-6*(1138292197363/250000000000:ℝ)+4*(1138292197363/250000000000:ℝ)^2)*(92462209897/4000000000000:ℝ) by norm_num).trans (h u hu)

theorem thetaTwelfth_cell_curvature_095 :
    ∀ u ∈ Set.Icc (95/512:ℝ) (3/16:ℝ), (80121097504047355743007/62500000000000000000000:ℝ) ≤ thetaFirstModeSecond u := by
  have hlo : (4570989388233/1000000000000:ℝ) ≤ Real.pi*Real.exp (2*(3/16:ℝ)) := by
    calc
      _ ≤ (3141592/1000000:ℝ)*∑ i ∈ Finset.range 20, (2*(3/16:ℝ))^i/i.factorial := by
        norm_num [Finset.sum_range_succ]
      _ ≤ _ := mul_le_mul (by linarith [Real.pi_gt_d6])
        (Real.sum_le_exp_of_nonneg (by norm_num) 20)
        (Finset.sum_nonneg (fun i _ => by positivity)) Real.pi_pos.le
  have h := thetaFirstModeSecond_endpoint_cell_lower (95/512:ℝ) (3/16:ℝ) (4570989388233/1000000000000:ℝ) (2272945399673/100000000000000:ℝ)
    (by norm_num) (by norm_num) hlo (by norm_num) (thetaFirstMode_refined_node_0288).1
  intro u hu
  exact (show (80121097504047355743007/62500000000000000000000:ℝ) ≤ (1/4-6*(4570989388233/1000000000000:ℝ)+4*(4570989388233/1000000000000:ℝ)^2)*(2272945399673/100000000000000:ℝ) by norm_num).trans (h u hu)

end CarrySelfAdjointOperator
