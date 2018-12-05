
%	RUN_R2U2: execute R2U2 on batch input data and plot results

%	FN	name of formula file(s), including .txt and .in for inputs
%

%sclear all;

function [a,pt_results,ft_results,ft_a_results, d, ft_a_times, signals] = run_r2u2(FN, INPUT)

plot_timesteps = true;

current_dir = pwd;

% Some directory sanity checking first
if (exist(FN) ~= 7),
  disp(['Directory ' FN ' does not exist. Exiting']);
  return;
end;

if (exist(['_Inputs/' INPUT '.dat']) ~= 2)
  disp(['Input ' INPUT ' .dat does not exist. Exiting']);
  return;
end;

if (exist([FN '/r2u2.oct']) == 0)
  disp(['R2U2 executable for test ' FN ' does not exist. Exiting']);
  exist([FN '/r2u2.oct'])
  return;
end;


cd(FN);

load(['../_Inputs/' INPUT '.dat']);


actual_num_atomics = max(sum(in'));
num_timesteps = size(in,1);

% Generate .trc file as well
trc_file = fopen([FN '.trc'], 'w');
for i=1:num_timesteps
fprintf(trc_file, '%d%d\n', in(i,1), in(i,2));
end;
fclose(trc_file);

[a,pt_results,ft_results,ft_a_results, d] = r2u2(in');


f=fopen([FN '.maps'],'r');
signals=textscan(f,'%d %d %s');
fclose(f);

N_signals = length(signals{1});

figure;
set(0,'DefaultTextInterpreter','none');
sig_id=signals{2}+1;
sig_t=signals{1};

% Fixed a small bug where the last time step was not being displayed
numtimesteps = size(pt_results,1);
pt_results(numtimesteps+1,:) = pt_results(numtimesteps,:);
ft_results(numtimesteps+1,:) = ft_results(numtimesteps,:);


hL=zeros(N_signals,1);hL2 = hL;
for i=1:N_signals,
	plot([1,size(pt_results,1)], [1+3*(N_signals -i),1+3*(N_signals -i)],'k-');
  hold on;
	if (sig_t(i)==0),
	  hL(i) = stairs(1+3*(N_signals -i) + pt_results(:,sig_id(i)),'g','linewidth',2);
	else
	  hL(i) = stairs(1+3*(N_signals -i) + ft_a_results(:,sig_id(i)),'b','linewidth',2);
	  hL2(i) = stairs(1+3*(N_signals -i) + ft_results(:,sig_id(i)),'r','linewidth',2);

	end;
end;

												 
axis([1,size(pt_results,1),0,3*N_signals+1]);

set(gca,'YTick',[1:3*N_signals+1]);
set(gca','YTickLabel',{'F','T','M'});

% Plot timesteps
if (plot_timesteps == false) then
  hLeg=legend(hL,signals{3},'location','eastoutside');
  return;
end;

legend_labels={'Synchronous', 'Asynchronous'};
hLeg = legend([hL2(1) hL(1)], legend_labels, 'location', 'southeastoutside');
legend('boxoff');

signal_names = signals{3};
for i = 1:N_signals,
  text(numtimesteps+1.5, 2.5+3*(N_signals -i), signal_names(i),'HorizontalAlignment','left','fontsize', 12);
end;

resolution = 0.1;

set(gca,'XTick',[]);
set(gca,'XColor','w');

YTick_value = [repmat(['F'; 'T'; 'M'], N_signals, 1); ' '; ' '];
set(gca,'YTickLabel',YTick_value);

axis([1,size(pt_results,1),-1.0,2+3*N_signals]);
%plot([1,size(pt_results,1)], [1+3*(N_signals),1+3*(N_signals -i)],'k-');


Yoffset = 3*N_signals+1;

timesteps = 1:numtimesteps;
plotX = 1:resolution:numtimesteps+1-resolution;
plotY1 = mod(floor(plotX),2);
plotY2 = 1-plotY1;

plotY1 += Yoffset;
plotY2 += Yoffset;

% Change to 'stairs' if want flat transition
plot(plotX, [plotY1' plotY2'],'linewidth',1,'color','k');
plot(plotX, [plotY1'-Yoffset-1.0 plotY2'-Yoffset-1.0],'linewidth',1,'color','k');


% Set a fontsize based on the number of digits to be displayed
fontsize = 12 - length(num2str(numtimesteps-1))*2;


yL = get(gca, 'YLim');
for i=1:numtimesteps
    text(i+0.4, 0.5+Yoffset, num2str(i),'HorizontalAlignment','center','fontsize', fontsize);
    text(i+0.4, -0.5, num2str(i),'HorizontalAlignment','center','fontsize', fontsize);
    line([i i],yL,'Color','k','LineStyle','--','LineWidth',1);
end;

text(numtimesteps/2, -2, [FN '.txt, ' INPUT '.dat'], 'HorizontalAlignment','center','fontsize',12);

printf('\n\nContents of %s.txt\n', FN);
input_file = fileread([FN '.txt'])

cd(current_dir);